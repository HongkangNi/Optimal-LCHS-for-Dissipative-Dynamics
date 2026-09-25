#!/usr/bin/env bash
# Build the project from a copy on /tmp (local disk), because /workspaces is a
# slow loop device.  Sources stay in the workspace and are symlinked in, so
# edits there are picked up directly.
#
# /tmp is wiped when the Codespace restarts.  If a snapshot made by
# scripts/save-build-snapshot.sh exists on the persistent disk, the build
# directory is restored from it (about a minute); otherwise dependencies are
# fetched again (about five minutes).
#
# usage: scripts/fast-build.sh [lake build target ...]
set -euo pipefail
# elan is only on PATH in login shells; make the script work from any terminal.
export PATH="$HOME/.elan/bin:/opt/conda/bin:$PATH"
SRC=$(cd "$(dirname "$0")/.." && pwd)
DST=${LCHS_FAST_DIR:-/tmp/lchs-fast}
SNAPSHOT=${LCHS_SNAPSHOT:-$SRC/.lake/fast-snapshot.tar.zst}

mkdir -p "$DST"
cp "$SRC"/lakefile.toml "$SRC"/lake-manifest.json "$SRC"/lean-toolchain "$DST"/
for f in LCHSWiener LCHSWiener.lean; do
  if [ -e "$DST/$f" ] && [ ! -L "$DST/$f" ]; then rm -rf "${DST:?}/$f"; fi
  ln -sfn "$SRC/$f" "$DST/$f"
done

cd "$DST"
if [ ! -d .lake/packages/mathlib ] && [ -f "$SNAPSHOT" ] && command -v zstd >/dev/null; then
  echo "Restoring build directory from $SNAPSHOT ..."
  zstd -dc "$SNAPSHOT" | tar -xf -
fi
if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Basic.olean ]; then
  lake exe cache get
fi
lake build "$@"
