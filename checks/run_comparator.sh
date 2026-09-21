#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
project_dir="$(pwd -P)"
test "$(id -u)" -ne 0
comparator_bin="$(command -v comparator)"
export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$(command -v landrun)}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$(command -v lean4export)}"
mkdir -p .lake
systemd-run --user --wait --pipe \
  --property='RestrictAddressFamilies=AF_NETLINK' \
  -E "PATH=$PATH" \
  -E "COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
  -E "COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
  --working-directory "$project_dir" \
  bwrap --unshare-user --uid "$(id -u)" --gid "$(id -g)" \
  --ro-bind / / --bind "$project_dir/.lake" "$project_dir/.lake" \
  --dev /dev --proc /proc --chdir "$project_dir" \
  lake env "$comparator_bin" comparator.json
