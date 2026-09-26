#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

# The workspace's compiler is selected by its root lean-toolchain. Mathlib is
# pinned independently by lake-manifest.json. Other dependencies' own
# lean-toolchain files describe their upstream projects and must not be
# rewritten or required to match this workspace's compiler declaration.
python3 tools/infra/assert_v428_toolchain_freeze.py
