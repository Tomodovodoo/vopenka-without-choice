#!/usr/bin/env bash
# Linux host entry point. The service runs as the caller with AF_UNIX disabled.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
config=${1:?Pass a Comparator configuration path}
sudo systemd-run --wait --pipe --uid="$(id -u)" \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$root" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="ELAN_HOME=${ELAN_HOME:-$HOME/.elan}" \
  bash scripts/verify-comparator.sh "$config"
