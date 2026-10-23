#/bin/sh

set -e

cargo run --locked --release --no-default-features --features=zk,backend_plonky2,disk_cache --bin mainpod_circuit_info -- $1
