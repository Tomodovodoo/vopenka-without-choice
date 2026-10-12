#!/usr/bin/env bash
# Comparator and independent kernels come from the pinned Lean toolchain.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
config=${1:-comparator-palomar.json}
for command in bwrap lake lean python3; do
  command -v "$command" >/dev/null || { echo "Missing command: $command" >&2; exit 1; }
done
prefix=$(lean --print-prefix)
for tool in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "Pinned toolchain lacks $tool" >&2; exit 1; }
done
python3 scripts/check-repository.py --config "$config"
mkdir -p .cache/verification
checked_config=$(mktemp "${TMPDIR:-/tmp}/zfvp-comparator.XXXXXX.json")
trap 'rm -f "$checked_config"' EXIT
python3 - "$config" "$checked_config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys
source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron'],
}
Path(destination).write_text(json.dumps(config, indent=2)+'\n')
PY
mapfile -t roots < <(python3 scripts/mathlib-cache-roots.py)
lake exe cache get "${roots[@]}"
lake comparator --config "$checked_config" 2>&1 | tee ".cache/verification/$(basename "$config" .json).log"
