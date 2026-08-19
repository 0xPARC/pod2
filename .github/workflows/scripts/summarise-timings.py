#!/usr/bin/env python3
"""Aggregate pod2/plonky2 timing lines into a per-scope summary.

Recognises two line shapes:

    timed "MainPod::prove": 7.068943638s          <- pod2's `timed!` macro
    [.. DEBUG plonky2::util::timing] 0.5s to fft  <- plonky2's TimingTree

Usage:
    summarise-timings.py [log]              per-scope totals (stdin if no arg)
    summarise-timings.py base.log other.log compare two runs, scope by scope

Tests run in parallel unless --test-threads=1 is passed, in which case samples
interleave and cannot be attributed to a test. Totals across the run still tell
you where the time goes, which is the point.
"""
import re
import sys
from collections import defaultdict

POD2 = re.compile(r'timed "([^"]+)": ([0-9.]+)(ms|µs|us|ns|s)\b')
PLONKY2 = re.compile(r"(?:\| )*([0-9.]+)s to (.+?)\s*$")
UNIT = {"s": 1.0, "ms": 1e-3, "us": 1e-6, "µs": 1e-6, "ns": 1e-9}


def parse(lines):
    totals = defaultdict(list)
    for line in lines:
        m = POD2.search(line)
        if m:
            totals[m.group(1)].append(float(m.group(2)) * UNIT[m.group(3)])
            continue
        if "util::timing" in line or line.lstrip().startswith("| "):
            m = PLONKY2.search(line)
            if m:
                totals[m.group(2)].append(float(m.group(1)))
    return totals


def summarise(totals):
    rows = sorted(totals.items(), key=lambda kv: -sum(kv[1]))
    print(f"{'scope':<44}{'n':>5}{'total':>11}{'mean':>10}{'max':>10}")
    print("-" * 80)
    for name, xs in rows:
        print(
            f"{name[:43]:<44}{len(xs):>5}{sum(xs):>10.2f}s"
            f"{sum(xs) / len(xs):>9.2f}s{max(xs):>9.2f}s"
        )


def compare(base, other, base_name, other_name):
    # Compare totals per scope. A scope missing from one side is reported as
    # such rather than as a delta, since that means the runs were not
    # equivalent and any percentage would be meaningless.
    names = sorted(set(base) | set(other), key=lambda n: -sum(base.get(n, [0])))
    print(f"{'scope':<44}{base_name:>11}{other_name:>11}{'delta':>10}")
    print("-" * 76)
    for name in names:
        if name not in base or name not in other:
            side = base_name if name in base else other_name
            print(f"{name[:43]:<44}{'(only in ' + side + ')':>32}")
            continue
        a, b = sum(base[name]), sum(other[name])
        delta = f"{(b - a) / a * 100:+.1f}%" if a > 0 else "n/a"
        print(f"{name[:43]:<44}{a:>10.2f}s{b:>10.2f}s{delta:>10}")


if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) == 2:
        with open(args[0]) as f:
            base = parse(f)
        with open(args[1]) as f:
            other = parse(f)
        if not base or not other:
            sys.exit("no timing lines found in one of the logs")
        compare(base, other, "base", "avx2")
    else:
        src = open(args[0]) if args else sys.stdin
        totals = parse(src)
        if not totals:
            sys.exit(
                "no timing lines found "
                "(did you pass --features time and --nocapture?)"
            )
        summarise(totals)
