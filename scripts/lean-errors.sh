#!/usr/bin/env bash
# Build one target (default: the whole library) via scripts/fast-build.sh and
# print only the errors, which is what matters while iterating on a proof.
#
# usage: scripts/lean-errors.sh [lake build target]
set -uo pipefail
SRC=$(cd "$(dirname "$0")/.." && pwd)
"$SRC/scripts/fast-build.sh" "${1:-LCHSWiener}" 2>&1 | python3 -c '
import re, sys
out = sys.stdin.read()
blocks = re.split(r"\n(?=(?:error|warning|trace|info|✖|⚠|✔|Some required|\[))", out)
for b in blocks:
    if b.startswith("error") or "build failed" in b:
        print(b[:2500])
    elif b.startswith("✖"):
        print(b.split("\n")[0])
'
