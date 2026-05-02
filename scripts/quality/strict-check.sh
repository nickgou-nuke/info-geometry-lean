#!/usr/bin/env bash
set -euo pipefail

STRICT_CHECK_ARTIFACT_DIR="${STRICT_CHECK_ARTIFACT_DIR:-artifacts/leantrail}"
mkdir -p "$STRICT_CHECK_ARTIFACT_DIR"

STRICT_CHECK_STDOUT_LOG="${STRICT_CHECK_STDOUT_LOG:-$STRICT_CHECK_ARTIFACT_DIR/strict-check.stdout.log}"
STRICT_CHECK_STDERR_LOG="${STRICT_CHECK_STDERR_LOG:-$STRICT_CHECK_ARTIFACT_DIR/strict-check.stderr.log}"
STRICT_CHECK_FAILURE_OUT="${STRICT_CHECK_FAILURE_OUT:-$STRICT_CHECK_ARTIFACT_DIR/failed_transitions.jsonl}"
STRICT_CHECK_FAILURE_REPORT="${STRICT_CHECK_FAILURE_REPORT:-$STRICT_CHECK_ARTIFACT_DIR/failure_harvest_strict_report.json}"
STRICT_CHECK_HARVEST_WARNINGS="${STRICT_CHECK_HARVEST_WARNINGS:-0}"

: >"$STRICT_CHECK_STDOUT_LOG"
: >"$STRICT_CHECK_STDERR_LOG"

exec > >(tee -a "$STRICT_CHECK_STDOUT_LOG")
exec 2> >(tee -a "$STRICT_CHECK_STDERR_LOG" >&2)

harvest_strict_failures_on_exit() {
  local exit_code=$?
  if [[ $exit_code -eq 0 ]]; then
    return 0
  fi
  echo "[strict-check] build failed; harvesting failed transitions from strict-check logs"
  harvest_cmd=(
    python3 tools/leantrail/failure_harvester.py
    --defects artifacts/dag/process-flow/defects.jsonl
    --build-stdout "$STRICT_CHECK_STDOUT_LOG"
    --build-stderr "$STRICT_CHECK_STDERR_LOG"
    --out "$STRICT_CHECK_FAILURE_OUT"
    --json-out "$STRICT_CHECK_FAILURE_REPORT"
    --merge-existing
  )
  if [[ "$STRICT_CHECK_HARVEST_WARNINGS" == "1" ]]; then
    harvest_cmd+=(--include-warnings)
  fi
  if ! "${harvest_cmd[@]}"; then
    echo "[strict-check] warning: failed to harvest strict-check failure memory" >&2
  fi
}
trap harvest_strict_failures_on_exit EXIT

echo "[strict-check] building modular libraries"
python3 tools/run_locked_lake_build.py --wait-for-build-lock InfoGeometryMeta
python3 tools/run_locked_lake_build.py --wait-for-build-lock InfoGeometryCanonical --wfail
python3 tools/run_locked_lake_build.py --wait-for-build-lock InfoGeometryLLM --wfail

echo "[strict-check] elaborating InfoGeometry/Library.lean"
lake env lean lean/InfoGeometry/Library.lean

echo "[strict-check] elaborating canonical root InfoGeometry.lean"
lake env lean lean/InfoGeometry.lean

CANONICAL_PATHS=(lean/InfoGeometry.lean lean/InfoGeometry/Library.lean lean/InfoGeometry/Canonical)

echo "[strict-check] ensuring archive file is not imported by canonical modules"
if rg -n "all_lean_files_combined" "${CANONICAL_PATHS[@]}" -g '*.lean'; then
  echo "[strict-check] archive file must not be imported by canonical modules"
  exit 1
fi

echo "[strict-check] ensuring canonical modules do not import experimental umbrella"
if rg -n "^import InfoGeometry\\.Experimental$" \
  "${CANONICAL_PATHS[@]}" -g '*.lean'; then
  echo "[strict-check] canonical modules must not import InfoGeometry.Experimental"
  exit 1
fi

echo "[strict-check] enforcing canonical-to-research import allowlist"
ALLOWED_CANONICAL_RESEARCH_IMPORTS=()

mapfile -t canonical_research_import_lines < <(
  rg -n "^import InfoGeometry\\.Research\\.[A-Za-z0-9_.]+$" \
    "${CANONICAL_PATHS[@]}" -g '*.lean' || true
)

violations=()
for line in "${canonical_research_import_lines[@]}"; do
  mod=$(echo "$line" | sed -E 's/.*import (InfoGeometry\.Research\.[A-Za-z0-9_.]+).*/\1/')
  allowed=false
  for ok in "${ALLOWED_CANONICAL_RESEARCH_IMPORTS[@]}"; do
    if [[ "$mod" == "$ok" ]]; then
      allowed=true
      break
    fi
  done
  if [[ "$allowed" == false ]]; then
    violations+=("$line")
  fi
done

if [[ ${#violations[@]} -gt 0 ]]; then
  echo "[strict-check] disallowed canonical->research imports found:"
  printf '%s\n' "${violations[@]}"
  exit 1
fi

echo "[strict-check] checking for unresolved placeholder markers"
if rg -n "content will be moved here" "${CANONICAL_PATHS[@]}" -g '*.lean'; then
  echo "[strict-check] placeholder content detected"
  exit 1
fi

echo "[strict-check] enforcing frontier integrity gate (no sorry/admit/axiom/postulate)"
python3 tools/quality/check_frontier_integrity_gate.py \
  --config tools/quality/frontier_gate.json \
  --json-out reports/dag/frontier-gate-report.json

CLOSURE_SPINE_PATHS=(
  lean/InfoGeometry/Canonical/CertifiedModularReduction.lean
  lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean
  lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean
  lean/InfoGeometry/Canonical/Cl11LorentzAction.lean
  lean/InfoGeometry/Canonical/BogoliubovOptimalTransport.lean
  lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean
  lean/InfoGeometry/Canonical/UhlmannBuresHolonomy.lean
  lean/InfoGeometry/Canonical/WindingOrbitClosure.lean
)

echo "[strict-check] enforcing closure-spine non-shadow policy (no finite-dimensional/matrix toys)"
if rg -n "FiniteDimensional|\\bMatrix\\b" "${CLOSURE_SPINE_PATHS[@]}"; then
  echo "[strict-check] closure spine must remain operator-level (no finite-dimensional/matrix assumptions)"
  exit 1
fi

echo "[strict-check] strict building frontier trunks with warnings as errors"
python3 tools/run_locked_lake_build.py --wait-for-build-lock --wfail \
  InfoGeometry.Canonical.WindingOrbitClosure \
  InfoGeometry.Canonical.ChiralOperatorConeClosure \
  InfoGeometry.Canonical.KKTCore \
  InfoGeometry.Canonical.KKTClosureSymmetry \
  InfoGeometry.Canonical.ClosureDrazinBridge \
  InfoGeometry.Canonical.DrazinInfiniteCore \
  InfoGeometry.Canonical.DrazinWitnessElimination \
  InfoGeometry.Canonical.DrazinSpectralBridge \
  InfoGeometry.Canonical.DrazinSpectralProjectorBridge \
  InfoGeometry.Canonical.DrazinSupercharge \
  InfoGeometry.Canonical.RelativeModularScaleShapeSplit \
  InfoGeometry.Canonical.ModularKLDivergenceBridge \
  InfoGeometry.Canonical.KMSSinkhornSeedState \
  InfoGeometry.Canonical.ThermodynamicGenerator \
  InfoGeometry.Canonical.ThermodynamicClosureTargets

echo "[strict-check] enforcing quarantine boundary"
bash scripts/enforce_quarantine_imports.sh

echo "[strict-check] enforcing agentic autonomy policy"
python3 tools/infra/agentic_policy_lint.py

echo "[strict-check] running constructivity audit on stable surface"
python3 tools/quality/audit_constructivity.py --mode stable

echo "[strict-check] running functorial invariance and core isomorphism tracing audit"
python3 tools/quality/functorial_invariance_audit.py \
  --json-out reports/dag/functorial-invariance-audit.json \
  --md-out reports/dag/functorial-invariance-audit.md

echo "[strict-check] refreshing maintained equivalence dictionary"
python3 tools/infra/generate_equivalence_dictionary.py \
  --curated-json docs/NameEquivalenceRegistry.json \
  --json-out reports/dag/equivalence-dictionary.json \
  --md-out reports/dag/equivalence-dictionary.md

echo "[strict-check] enforcing equivalence dictionary unresolved-growth gate"
python3 tools/quality/check_equivalence_dictionary_gate.py \
  --report reports/dag/equivalence-dictionary.json \
  --policy tools/quality/equivalence_dictionary_gate.json

echo "[strict-check] enforcing translation registry anchors"
python3 tools/quality/check_translation_registry.py \
  --registry docs/OperatorTheoremTranslationRegistry.md \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.operatorialKMSCondition_lorentzBivectorSeed_of_structural \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit \
  --required-anchor InfoGeometry.Canonical.ModularSuperchargeClosure.projectedEvenGenerator_fixed_under_lorentzWedgeOrbit \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_eq_gOnePart \
  --required-anchor InfoGeometry.Canonical.KKTCore.uPlus_mul_uPlus_eq_zero \
  --required-anchor InfoGeometry.Canonical.KKTCore.commutator_uPlus_uMinus_isGZero

echo "[strict-check] enforcing closure debt frontier gate"
python3 tools/quality/check_closure_debt_gate.py \
  --policy tools/quality/closure_debt_gate.json

CLOSURE_DEBT_BUILD_TARGETS=(
  InfoGeometry.Core.CartanPhaseAxisForcing
  InfoGeometry.Canonical.WindingOrbitClosure
  InfoGeometry.Quantum.ModularAnomaly
  InfoGeometry.Canonical.DrazinWeylConstructive
  InfoGeometry.Quantum.TriadicWeylBridge
  InfoGeometry.LLM.TrialityMoE
  InfoGeometry.LLM.SinkhornDefectFlow
)

echo "[strict-check] strict-building closure-debt target trunks"
for target in "${CLOSURE_DEBT_BUILD_TARGETS[@]}"; do
  echo "  - lake build ${target}"
  lake build "${target}"
done

echo "[strict-check] enforcing Pauli seal directives (I-XI) on canonical surface"
python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json

echo "[strict-check] running surrogate dependency audit"
scripts/audit_surrogates.sh

echo "[strict-check] OK"
QUALITY_REPORT_DIR="${STRICT_CHECK_REPORT_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/info-geometry-quality.XXXXXX")}"
mkdir -p "$QUALITY_REPORT_DIR"

run_advisory_audit() {
  local name="$1"
  shift
  local log_path="${QUALITY_REPORT_DIR}/${name}.log"
  "$@" >"$log_path" 2>&1
  local status=$?
  if [[ $status -eq 0 ]]; then
    echo "[strict-check] ${name} audit passed"
  else
    echo "[strict-check] ${name} audit reported advisory findings; see ${log_path}"
  fi
  return $status
}

echo "[strict-check] running naming convention audit (advisory)"
set +e
run_advisory_audit naming python3 tools/quality/audit_naming.py lean/InfoGeometry/Canonical
naming_status=$?
echo "[strict-check] running docstring audit (advisory)"
run_advisory_audit docstrings python3 tools/quality/audit_docstrings.py lean/InfoGeometry/Canonical
docstring_status=$?
echo "[strict-check] running style audit (advisory)"
run_advisory_audit style python3 tools/quality/audit_style.py lean/InfoGeometry/Canonical
style_status=$?
set -e

if [[ $naming_status -ne 0 || $docstring_status -ne 0 || $style_status -ne 0 ]]; then
  echo "[strict-check] advisory quality audits reported findings:"
  echo "  naming audit exit code: $naming_status"
  echo "  docstring audit exit code: $docstring_status"
  echo "  style audit exit code: $style_status"
  echo "  logs: $QUALITY_REPORT_DIR"
  if [[ "${STRICT_CHECK_ENFORCE_HEURISTICS:-0}" == "1" ]]; then
    echo "[strict-check] failing because STRICT_CHECK_ENFORCE_HEURISTICS=1"
    exit 1
  fi
fi

echo "[strict-check] running compiler bridge RPC regression tests"
python3 -m unittest tests.test_compiler_bridge_rpc

echo "[strict-check] all enforced checks passed"
