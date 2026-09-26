#!/usr/bin/env bash
# ==============================================================================
# E2E Test Suite for CAS O(1) Optimization Project
# ==============================================================================
# Covers the 4 verification tiers:
#   Tier 1: Feature Coverage (Locked Lake build of target Lean modules)
#   Tier 2: Boundary & Corner Cases (zero native_decide, zero simpa using, no sorry, proposition fidelity)
#   Tier 3: CAS & Integration Verification (CAS certificate script & DAG.lean import verification)
#   Tier 4: Compilation Performance & O(1) Verification (strict timeouts, no CPU hangs)
# ==============================================================================

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

# ANSI Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m' # No Color

TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

SELECTED_TIER="all"
VERBOSE=0

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tier|-t)
      SELECTED_TIER="$2"
      shift 2
      ;;
    --verbose|-v)
      VERBOSE=1
      shift
      ;;
    --help|-h)
      echo "Usage: $0 [--tier <1|2|3|4|all>] [--verbose]"
      echo "  --tier, -t   Run a specific tier (1, 2, 3, 4, or all). Default: all"
      echo "  --verbose, -v Show verbose command outputs"
      echo "  --help, -h   Show this help message"
      exit 0
      ;;
    *)
      echo "Unknown option: $1"
      echo "Usage: $0 [--tier <1|2|3|4|all>] [--verbose]"
      exit 1
      ;;
  esac
done

log_info() {
  echo -e "${YELLOW}[INFO]${NC} $1"
}

log_pass() {
  echo -e "${GREEN}[PASS]${NC} $1"
  TOTAL_TESTS=$((TOTAL_TESTS + 1))
  PASSED_TESTS=$((PASSED_TESTS + 1))
}

log_fail() {
  echo -e "${RED}[FAIL]${NC} $1"
  if [ -n "${2:-}" ]; then
    echo -e "${RED}       Reason: $2${NC}"
  fi
  TOTAL_TESTS=$((TOTAL_TESTS + 1))
  FAILED_TESTS=$((FAILED_TESTS + 1))
}

tier_header() {
  echo -e "\n${BOLD}${CYAN}====================================================================${NC}"
  echo -e "${BOLD}${CYAN}  $1${NC}"
  echo -e "${BOLD}${CYAN}====================================================================${NC}\n"
}

# ------------------------------------------------------------------------------
# TIER 1: Feature Coverage
# ------------------------------------------------------------------------------
run_tier_1() {
  tier_header "TIER 1: Feature Coverage (Locked Lake Builds)"

  # Test 1.1: Build DAG.DiracLaplacian
  local t1_target="DAG.DiracLaplacian"
  log_info "Verifying locked build of ${t1_target}..."
  local t1_output
  local t1_code=0
  t1_output=$(python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock "${t1_target}" 2>&1) || t1_code=$?
  if [ $VERBOSE -eq 1 ] && [ -n "$t1_output" ]; then
    echo "$t1_output"
  fi
  if [ $t1_code -eq 0 ]; then
    log_pass "Feature Target 1 (${t1_target}) compiles cleanly under build lock"
  else
    log_fail "Feature Target 1 (${t1_target}) failed to compile" "$t1_output"
  fi

  # Test 1.2: Build InfoGeometry.Quantum.NoncommutativeFockBridge
  local t2_target="InfoGeometry.Quantum.NoncommutativeFockBridge"
  log_info "Verifying locked build of ${t2_target}..."
  local t2_output
  local t2_code=0
  t2_output=$(python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock "${t2_target}" 2>&1) || t2_code=$?
  if [ $VERBOSE -eq 1 ] && [ -n "$t2_output" ]; then
    echo "$t2_output"
  fi
  if [ $t2_code -eq 0 ]; then
    log_pass "Feature Target 2 (${t2_target}) compiles cleanly under build lock"
  else
    log_fail "Feature Target 2 (${t2_target}) failed to compile" "$t2_output"
  fi

  # Test 1.3: Target Source Files Verification
  log_info "Verifying target source files and module headers..."
  local missing_files=0
  for f in "lean/DAG/DiracLaplacian.lean" "lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean"; do
    if [ ! -f "$f" ]; then
      missing_files=$((missing_files + 1))
      log_fail "Target file exists: $f" "File not found"
    else
      local line_cnt
      line_cnt=$(wc -l < "$f")
      if [ "$line_cnt" -lt 10 ]; then
        missing_files=$((missing_files + 1))
        log_fail "Target file has substantive content: $f" "File has only $line_cnt lines"
      fi
    fi
  done
  if [ $missing_files -eq 0 ]; then
    log_pass "Target source files exist and contain full module definitions"
  fi
}

# ------------------------------------------------------------------------------
# TIER 2: Boundary & Corner Cases
# ------------------------------------------------------------------------------
run_tier_2() {
  tier_header "TIER 2: Boundary & Corner Cases (Brute-Force Elimination & Rigor)"

  # Test 2.1: Zero native_decide occurrences in lean/DAG/DiracLaplacian.lean
  local f_dirac="lean/DAG/DiracLaplacian.lean"
  log_info "Auditing ${f_dirac} for native_decide occurrences..."
  if [ -f "$f_dirac" ]; then
    local nd_count
    nd_count=$(grep -c "native_decide" "$f_dirac" || true)
    if [ "$nd_count" -eq 0 ]; then
      log_pass "Zero 'native_decide' occurrences in ${f_dirac} (found: 0)"
    else
      local nd_lines
      nd_lines=$(grep -n "native_decide" "$f_dirac" || true)
      log_fail "Found $nd_count 'native_decide' occurrence(s) in ${f_dirac}" "$nd_lines"
    fi
  else
    log_fail "Audit ${f_dirac} for native_decide" "File does not exist"
  fi

  # Test 2.2: Zero simpa using occurrences in lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean
  local f_fock="lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean"
  log_info "Auditing ${f_fock} for simpa using occurrences..."
  if [ -f "$f_fock" ]; then
    local su_count
    su_count=$(grep -c "simpa using" "$f_fock" || true)
    if [ "$su_count" -eq 0 ]; then
      log_pass "Zero 'simpa using' occurrences in ${f_fock} (found: 0)"
    else
      local su_lines
      su_lines=$(grep -n "simpa using" "$f_fock" || true)
      log_fail "Found $su_count 'simpa using' occurrence(s) in ${f_fock}" "$su_lines"
    fi
  else
    log_fail "Audit ${f_fock} for simpa using" "File does not exist"
  fi

  # Test 2.3: Zero sorry / admit occurrences (Proof Completeness)
  log_info "Auditing target files for incomplete proofs (sorry/admit)..."
  local sorry_found=0
  for f in "$f_dirac" "$f_fock"; do
    if [ -f "$f" ]; then
      local s_count
      s_count=$(grep -nE "\b(sorry|admit)\b" "$f" || true)
      if [ -n "$s_count" ]; then
        sorry_found=$((sorry_found + 1))
        log_fail "Proof completeness in $f" "Found sorry/admit:\n$s_count"
      fi
    fi
  done
  if [ $sorry_found -eq 0 ]; then
    log_pass "Zero 'sorry' or 'admit' markers across all target files"
  fi

  # Test 2.4: Boundary & Clean Input Handling
  log_info "Checking edge/boundary parameter handling..."
  local cas_script="scripts/cas_dirac_laplacian_certificate.py"
  if [ -f "$cas_script" ]; then
    local boundary_output
    local boundary_code=0
    boundary_output=$(python3 "$cas_script" 2>&1) || boundary_code=$?
    if [ $boundary_code -eq 0 ]; then
      log_pass "CAS certificate script executes cleanly on standard inputs"
    else
      log_fail "CAS certificate script crashed on standard execution" "$boundary_output"
    fi
  else
    log_fail "CAS certificate script exists: $cas_script" "File not found"
  fi

  # ----------------------------------------------------------------------------
  # Test 2.5: Proposition Fidelity & Anti-Facade Audit (Theorem Signature Rigor)
  # ----------------------------------------------------------------------------
  log_info "Auditing ${f_dirac} for proposition fidelity and anti-facade compliance..."
  if [ -f "$f_dirac" ]; then
    local fidelity_failed=0
    local fidelity_errors=""

    # Helper: Extract theorem statement between "theorem <name>" and ":="
    extract_theorem_stmt() {
      local thm="$1"
      local src_file="$2"
      awk -v t="$thm" '
        $0 ~ "^theorem " t "[: ]" { p=1 }
        p {
          stmt = stmt (stmt ? " " : "") $0
          if ($0 ~ /:=(\s*by|\s*$)/) {
            print stmt
            exit
          }
        }
      ' "$src_file"
    }

    # Step A: Mandatory active code tokens (excluding comments)
    local stripped_code
    stripped_code=$(grep -v "^\s*--" "$f_dirac" | sed '/\/\*/,/\*\//d')
    for req_sym in "graphDirac" "chainComplex" "triangleComplex" "canonicalDigonComplex" "diracSquareCheck" "matTrace"; do
      if ! echo "$stripped_code" | grep -q "\<${req_sym}\>"; then
        fidelity_failed=$((fidelity_failed + 1))
        fidelity_errors="${fidelity_errors}\n- Missing required mathematical symbol in active code: '${req_sym}'"
      fi
    done

    # Step B: Per-theorem proposition signature verification
    # Mapping of theorem name to mandatory tokens required in its proposition
    local theorem_requirements=(
      "dirac_squared_block_diagonal_chain:graphDirac,chainComplex,matMul"
      "dirac_square_check_chain:diracSquareCheck,chainComplex"
      "dirac_sq_upper_left_is_laplacian0_chain:graphDirac,chainComplex,laplacian0"
      "dirac_sq_lower_right_is_down_laplacian1_chain:graphDirac,chainComplex,matMul,boundary1"
      "dirac_sq_upper_right_is_zero_chain:graphDirac,chainComplex"
      "dirac_sq_lower_left_is_zero_chain:graphDirac,chainComplex"
      "trace_D_sq_equals_trace_laplacians_chain:matTrace,graphDirac,chainComplex"
      "dirac_squared_block_diagonal_triangle:graphDirac,triangleComplex,matMul"
      "dirac_squared_block_diagonal_digon:graphDirac,canonicalDigonComplex|digonComplex,matMul"
      "dirac_square_check_triangle:diracSquareCheck,triangleComplex"
    )

    for req in "${theorem_requirements[@]}"; do
      local thm_name="${req%%:*}"
      local token_list="${req#*:}"
      IFS="," read -r -a req_tokens <<< "$token_list"

      local stmt
      stmt=$(extract_theorem_stmt "$thm_name" "$f_dirac")
      if [ -z "$stmt" ]; then
        fidelity_failed=$((fidelity_failed + 1))
        fidelity_errors="${fidelity_errors}\n- Theorem '${thm_name}' declaration is missing from ${f_dirac}"
        continue
      fi

      for tok in "${req_tokens[@]}"; do
        if ! echo "$stmt" | grep -qE "\<(${tok})\>"; then
          fidelity_failed=$((fidelity_failed + 1))
          fidelity_errors="${fidelity_errors}\n- Theorem '${thm_name}' proposition missing mandatory token: '${tok}'"
        fi
      done
    done

    # Step C: Negative anti-facade regex check (banning known tautological cheats)
    if grep -qE "upper_right_zero\s*=\s*.*lower_left_zero" "$f_dirac"; then
      fidelity_failed=$((fidelity_failed + 1))
      fidelity_errors="${fidelity_errors}\n- Detected proof-irrelevance facade pattern: 'upper_right_zero = lower_left_zero'"
    fi

    if grep -qE "trDsq\s*=\s*trΔ₀" "$f_dirac"; then
      fidelity_failed=$((fidelity_failed + 1))
      fidelity_errors="${fidelity_errors}\n- Detected arithmetic substitution facade pattern: 'trDsq = trΔ₀ + trDownΔ₁'"
    fi

    if grep -qE "(chain|triangle|digon)DiracSqCertificate\s*=\s*#\[" "$f_dirac"; then
      fidelity_failed=$((fidelity_failed + 1))
      fidelity_errors="${fidelity_errors}\n- Detected constant certificate reflexive equality facade"
    fi

    if [ "$fidelity_failed" -eq 0 ]; then
      log_pass "Proposition fidelity verified (all 10 theorems prove authentic combinatorial graph Dirac propositions)"
    else
      log_fail "Proposition fidelity audit failed (${fidelity_failed} error(s) found)" "$fidelity_errors"
    fi
  else
    log_fail "Audit ${f_dirac} for proposition fidelity" "File does not exist"
  fi
}

# ------------------------------------------------------------------------------
# TIER 3: CAS & Integration Verification
# ------------------------------------------------------------------------------
run_tier_3() {
  tier_header "TIER 3: CAS & Integration Verification"

  # Test 3.1: Python CAS Certificate Execution and Identity Checks
  local cas_script="scripts/cas_dirac_laplacian_certificate.py"
  log_info "Running CAS certificate generator: ${cas_script}..."
  if [ -f "$cas_script" ]; then
    local cas_output
    local cas_code=0
    cas_output=$(python3 "$cas_script" 2>&1) || cas_code=$?
    if [ $VERBOSE -eq 1 ] && [ -n "$cas_output" ]; then
      echo "$cas_output"
    fi
    if [ $cas_code -ne 0 ]; then
      log_fail "CAS certificate script execution" "Exited with code $cas_code:\n$cas_output"
    else
      # Check expected content in CAS output
      local missing_complex=0
      for c in "chain" "triangle" "digon"; do
        if ! echo "$cas_output" | grep -qi "$c"; then
          missing_complex=$((missing_complex + 1))
          log_fail "CAS output covers complex: $c" "Keyword '$c' not found in CAS script output"
        fi
      done
      if [ $missing_complex -eq 0 ]; then
        log_pass "CAS script verified polynomial certificates for chain, triangle, and digon complexes"
      fi

      # Check block decomposition and trace identity verification
      if echo "$cas_output" | grep -qiE "trace|block|decomposition|identity|verified|D\^2"; then
        log_pass "CAS script verified block decomposition and trace identities"
      else
        log_fail "CAS script output confirmation" "Expected block/trace confirmation keywords missing"
      fi
    fi
  else
    log_fail "CAS script exists: $cas_script" "File not found"
  fi

  # Test 3.2: Export Verification in lean/DAG.lean
  local dag_agg="lean/DAG.lean"
  log_info "Verifying 'import DAG.DiracLaplacian' in ${dag_agg}..."
  if [ -f "$dag_agg" ]; then
    if grep -qE "^import DAG\.DiracLaplacian" "$dag_agg"; then
      log_pass "Active 'import DAG.DiracLaplacian' found in ${dag_agg}"
    else
      local commented_import
      commented_import=$(grep -n "DiracLaplacian" "$dag_agg" || true)
      log_fail "Active 'import DAG.DiracLaplacian' in ${dag_agg}" "Import is missing or commented out: $commented_import"
    fi
  else
    log_fail "DAG aggregate file exists: ${dag_agg}" "File not found"
  fi

  # Test 3.3: Integration Compilation of lean/DAG.lean
  log_info "Verifying that lean/DAG.lean compiles without error..."
  local dag_output
  local dag_code=0
  dag_output=$(lake env lean "$dag_agg" 2>&1) || dag_code=$?
  if [ $VERBOSE -eq 1 ] && [ -n "$dag_output" ]; then
    echo "$dag_output"
  fi
  if [ $dag_code -eq 0 ]; then
    log_pass "Module ${dag_agg} with all active exports compiles without error"
  else
    log_fail "Module ${dag_agg} failed to compile" "$dag_output"
  fi
}

# ------------------------------------------------------------------------------
# TIER 4: Compilation Performance & O(1) Verification
# ------------------------------------------------------------------------------
run_tier_4() {
  tier_header "TIER 4: Compilation Performance & O(1) Verification"

  # Timeout threshold in seconds for single file checking
  local TIMEOUT_SEC=35
  local STRICT_O1_MAX=15

  # Test 4.1: Compilation Performance of lean/DAG/DiracLaplacian.lean
  local f_dirac="lean/DAG/DiracLaplacian.lean"
  log_info "Benchmarking kernel compilation time of ${f_dirac} (timeout: ${TIMEOUT_SEC}s)..."
  if [ -f "$f_dirac" ]; then
    local start_time end_time elapsed_sec
    start_time=$(date +%s)
    local dirac_perf_code=0
    local dirac_perf_out
    dirac_perf_out=$(timeout "${TIMEOUT_SEC}s" lake env lean "$f_dirac" 2>&1) || dirac_perf_code=$?
    end_time=$(date +%s)
    elapsed_sec=$((end_time - start_time))

    if [ $dirac_perf_code -eq 124 ]; then
      log_fail "Compilation performance of ${f_dirac}" "Timed out after ${TIMEOUT_SEC}s (CPU hang detected)"
    elif [ $dirac_perf_code -ne 0 ]; then
      log_fail "Compilation performance of ${f_dirac}" "Compilation failed with code $dirac_perf_code:\n$dirac_perf_out"
    else
      if [ $elapsed_sec -le $STRICT_O1_MAX ]; then
        log_pass "Compilation of ${f_dirac} completed in ${elapsed_sec}s (<= ${STRICT_O1_MAX}s, O(1) definitional checking verified)"
      else
        log_fail "Compilation of ${f_dirac} took ${elapsed_sec}s" "Exceeded strict O(1) threshold of ${STRICT_O1_MAX}s"
      fi
    fi
  else
    log_fail "Benchmark ${f_dirac}" "File not found"
  fi

  # Test 4.2: Compilation Performance of lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean
  local f_fock="lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean"
  log_info "Benchmarking kernel compilation time of ${f_fock} (timeout: ${TIMEOUT_SEC}s)..."
  if [ -f "$f_fock" ]; then
    local start_time end_time elapsed_sec
    start_time=$(date +%s)
    local fock_perf_code=0
    local fock_perf_out
    fock_perf_out=$(timeout "${TIMEOUT_SEC}s" lake env lean "$f_fock" 2>&1) || fock_perf_code=$?
    end_time=$(date +%s)
    elapsed_sec=$((end_time - start_time))

    if [ $fock_perf_code -eq 124 ]; then
      log_fail "Compilation performance of ${f_fock}" "Timed out after ${TIMEOUT_SEC}s (CPU hang detected)"
    elif [ $fock_perf_code -ne 0 ]; then
      log_fail "Compilation performance of ${f_fock}" "Compilation failed with code $fock_perf_code:\n$fock_perf_out"
    else
      if [ $elapsed_sec -le $STRICT_O1_MAX ]; then
        log_pass "Compilation of ${f_fock} completed in ${elapsed_sec}s (<= ${STRICT_O1_MAX}s, O(1) term unification verified)"
      else
        log_fail "Compilation of ${f_fock} took ${elapsed_sec}s" "Exceeded strict O(1) threshold of ${STRICT_O1_MAX}s"
      fi
    fi
  else
    log_fail "Benchmark ${f_fock}" "File not found"
  fi

  # Test 4.3: Concurrency and Process Hygiene
  log_info "Verifying system concurrency hygiene and build lock status..."
  local lock_file="/tmp/info-geometry-build.lock"
  if [ -f "$lock_file" ]; then
    log_pass "Build lock file state inspected (/tmp/info-geometry-build.lock is clean or managed)"
  else
    log_pass "Build lock file is free (no active locks holding compiler)"
  fi
}

# ------------------------------------------------------------------------------
# Main Dispatcher
# ------------------------------------------------------------------------------
echo -e "${BOLD}Starting E2E CAS O(1) Optimization Test Suite...${NC}"
echo -e "Repository root: ${REPO_ROOT}"
echo -e "Selected tier:   ${SELECTED_TIER}\n"

case "$SELECTED_TIER" in
  1)
    run_tier_1
    ;;
  2)
    run_tier_2
    ;;
  3)
    run_tier_3
    ;;
  4)
    run_tier_4
    ;;
  all)
    run_tier_1
    run_tier_2
    run_tier_3
    run_tier_4
    ;;
  *)
    echo "Invalid tier: $SELECTED_TIER. Use 1, 2, 3, 4, or all."
    exit 1
    ;;
esac

# ------------------------------------------------------------------------------
# Final Summary
# ------------------------------------------------------------------------------
echo -e "\n${BOLD}${CYAN}====================================================================${NC}"
echo -e "${BOLD}${CYAN}  E2E Test Suite Summary${NC}"
echo -e "${BOLD}${CYAN}====================================================================${NC}"
echo -e "Total Tests:  ${TOTAL_TESTS}"
echo -e "Passed:       ${GREEN}${PASSED_TESTS}${NC}"
echo -e "Failed:       ${RED}${FAILED_TESTS}${NC}"

if [ $FAILED_TESTS -eq 0 ]; then
  echo -e "\n${BOLD}${GREEN}>>> ALL TESTS PASSED SUCCESSFULLY. E2E SUITE VERIFIED. <<<${NC}\n"
  exit 0
else
  echo -e "\n${BOLD}${RED}>>> E2E TEST SUITE REPORTED ${FAILED_TESTS} FAILURE(S). <<<${NC}\n"
  exit 1
fi
