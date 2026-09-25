#!/usr/bin/env bash
# Save the fast build directory (/tmp/lchs-fast/.lake) to the persistent disk,
# so that scripts/fast-build.sh can restore it quickly after a Codespace
# restart.  Mathlib's compiled files are excluded: `lake exe cache get`
# restores them from ~/.cache/mathlib, which is already on the persistent disk.
# Rerun this after the dependencies change; it takes a few seconds.
set -euo pipefail
export PATH="/opt/conda/bin:$PATH"
SRC=$(cd "$(dirname "$0")/.." && pwd)
DST=${LCHS_FAST_DIR:-/tmp/lchs-fast}
SNAPSHOT=${LCHS_SNAPSHOT:-$SRC/.lake/fast-snapshot.tar.zst}
cd "$DST"
tar -cf - --exclude=.lake/packages/mathlib/.lake/build/lib \
  --exclude=.lake/packages/mathlib/.lake/build/ir .lake |
  zstd -T0 -3 -q -f -o "$SNAPSHOT.tmp"
mv "$SNAPSHOT.tmp" "$SNAPSHOT"
ls -la "$SNAPSHOT"
