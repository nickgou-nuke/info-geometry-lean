#!/usr/bin/env bash
set -euo pipefail

echo "[strict-check] building InfoGeometry.Library with warnings as errors"
lake build InfoGeometry.Library --wfail

echo "[strict-check] elaborating InfoGeometry/Library.lean"
lake env lean InfoGeometry/Library.lean

echo "[strict-check] ensuring archive file is not imported by canonical modules"
if rg -n "all_lean_files_combined" InfoGeometry.lean InfoGeometry -g '*.lean'; then
  echo "[strict-check] archive file must not be imported by canonical modules"
  exit 1
fi

echo "[strict-check] checking for unresolved placeholders"
if rg -n "\\b(sorry|admit)\\b|content will be moved here" InfoGeometry.lean InfoGeometry -g '*.lean'; then
  echo "[strict-check] placeholder content detected"
  exit 1
fi

echo "[strict-check] OK"
