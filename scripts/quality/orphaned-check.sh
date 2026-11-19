#!/usr/bin/env bash
set -euo pipefail

# Canonical Lean source roots under lean/
ALLOWED_ROOT_DIRS=(Agent DAG Docs Experimental InfoGeometry Omega PrimitiveSetsAboveX SelfReference Socratic VirasoroProject docs lean sandbox scripts)
# Allowed top-level Lean modules and build config in lean/
ALLOWED_TOP_LEVEL_LEAN=(
  Agent.lean
  AuditNative.lean
  AuditNativeRun.lean
  AuditStrict.lean
  B3PresentedGroup.lean
  CheckBasis.lean
  CheckTemp.lean
  DAG.lean
  Docs.lean
  Experimental.lean
  GrandPartitionAll.lean
  GrandPartitionEuler.lean
  GrandPartitionOnline.lean
  GrandPartitionPolynomial.lean
  GrandPartitionProbability.lean
  GrandPartitionRational.lean
  GrandPartitionRobustPoisson.lean
  GrandPartitionTransform.lean
  GrandUnifiedNoncommutativeOperatorSynthesis.lean
  InfoGeometry.lean
  KaplanskyCliffordBridge.lean
  NonIsoConf3OrlikSolomon.lean
  Omega.lean
  PrimitiveSetsAboveX.lean
  SelfReference.lean
  Socratic.lean
  SplitOctonionBraidSU3.lean
  Test.lean
  TestFin.lean
  VirasoroProject.lean
  YangBaxterQSwap.lean
  YangBaxterZornBridge.lean
  ZornScalingFlow.lean
  ast_export_test.lean
  lakefile.lean
  temp_test.lean
  test_fixes2.lean
  test_reflection.lean
  test_rpow.lean
  test_selfconcordance.lean
)

is_allowed_top_level_lean() {
  local f="$1"
  for allowed in "${ALLOWED_TOP_LEVEL_LEAN[@]}"; do
    [[ "$f" == "$allowed" ]] && return 0
  done
  return 1
}

is_allowed_root_file() {
  local rel="$1"
  for d in "${ALLOWED_ROOT_DIRS[@]}"; do
    [[ "$rel" == "$d"/* ]] && return 0
  done
  return 1
}

# 1) top-level lean/ files must be known umbrella/standalone modules or build config
while IFS= read -r file; do
  fname=$(basename "$file")
  if [[ "$fname" == *.lean ]] && ! is_allowed_top_level_lean "$fname"; then
    echo "[orphaned-check] Orphaned top-level Lean file in lean/: $fname"
    exit 1
  fi
done < <(find lean/ -maxdepth 1 \( -type f -o -type l \))

# 2) all .lean files must live in allowed roots or be allowed top-level modules
while IFS= read -r file; do
  rel=${file#lean/}
  if is_allowed_top_level_lean "$rel"; then
    continue
  fi
  if ! is_allowed_root_file "$rel"; then
    echo "[orphaned-check] Orphaned Lean file: $file"
    exit 1
  fi
done < <(find lean/ \( -type f -o -type l \) -name '*.lean')

# 3) optionally check for empty dirs (excluding lean root)
EMPTY_DIRS=$(find lean/ -type d -empty | grep -vE '^lean/$|^lean$' || true)
if [[ -n "$EMPTY_DIRS" ]]; then
  echo "[orphaned-check] Empty directory found:"
  echo "$EMPTY_DIRS"
  exit 1
fi

echo "[orphaned-check] OK"
