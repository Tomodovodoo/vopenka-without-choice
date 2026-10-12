#!/usr/bin/env bash
# lake comparator supplies bubblewrap isolation and bundled kernels.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
exec bash "$root/scripts/verify-comparator.sh" "${1:-comparator-palomar.json}"
