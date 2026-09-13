#!/usr/bin/env bash
# Based on PalomarTemplate/scripts/verify-comparator.sh at
# 128a6c5ce5f48622e69927ccd639cbff401022e8, Apache-2.0.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cache=${PALOMAR_COMPARATOR_CACHE:-"$root/.cache/comparator-tools"}
for command in git lake go cargo python3; do
  command -v "$command" >/dev/null || { echo "Missing command: $command" >&2; exit 1; }
done
mkdir -p "$cache/bin" "$root/.cache/verification"
checkout() {
  local url=$1 directory=$2 revision=$3
  if [[ ! -d "$directory/.git" ]]; then
    git clone --filter=blob:none --no-checkout "$url" "$directory"
  fi
  git -C "$directory" fetch --depth 1 origin "$revision"
  git -C "$directory" checkout --detach "$revision"
  test "$(git -C "$directory" rev-parse HEAD)" = "$revision"
}
checkout https://github.com/leanprover/comparator "$cache/comparator" 2312244ac716564a61cc0bf4e107d9abf1757a61
checkout https://github.com/leanprover/lean4export "$cache/lean4export" cacf989bd75f608700820f6afc595f32e7a99a4d
checkout https://github.com/robsimmons/nanoda_lib "$cache/nanoda" 68d5ca9db226849b41a6fff59d796ff19d0a8840
for tool in comparator lean4export; do
  test "$(tr -d '[:space:]' < "$cache/$tool/lean-toolchain")" = "$(tr -d '[:space:]' < "$root/lean-toolchain")" || {
    echo "$tool toolchain does not match the project" >&2; exit 1;
  }
done
GOBIN="$cache/bin" go install github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd "$cache/comparator" && lake build comparator)
(cd "$cache/lean4export" && lake build lean4export)
(cd "$cache/nanoda" && cargo build --release --locked)
cd "$root"
lake exe cache get
export PALOMAR_LANDRUN_BIN="$cache/bin/landrun"
export COMPARATOR_LANDRUN="$root/scripts/landrun-wrapper.sh"
export COMPARATOR_LEAN4EXPORT="$cache/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$cache/nanoda/target/release/nanoda_bin"
# The caller must enforce the AF_UNIX restriction described in Comparator's
# README. CI runs this command inside an unprivileged systemd service.
lake env "$cache/comparator/.lake/build/bin/comparator" comparator.json 2>&1 | tee .cache/verification/comparator.log
