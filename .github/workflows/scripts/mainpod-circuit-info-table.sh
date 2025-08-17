#/bin/sh

set -e

# Generate the markdown table entry of the MainPod circuit information

scripts_dir=$(dirname "$0")
data=$(./${scripts_dir}/mainpod-circuit-info.sh circuit-info)
date=$(date --utc --iso-8601=minutes)
commit=$(git rev-parse HEAD)
params_hash=$(echo "$data" | jq --raw-output .params_hash)
verifier_hash=$(echo "$data" | jq --raw-output .verifier_hash)
common_hash=$(echo "$data" | jq --raw-output .common_hash)
echo "| $date | [\`${commit}\`](https://github.com/0xPARC/pod2/commit/${commit}) | [\`${params_hash}\`](https://raw.githubusercontent.com/wiki/0xPARC/pod2/params/${params_hash}.json) | \`${verifier_hash}\` | \`${common_hash}\` |"
