#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="/home/goutev/info-geometry-lean"
TARGET_FILE="$REPO_ROOT/lean/DAG/DiracLaplacian.lean"
TEST_DIR="/home/goutev/info-geometry-lean/.agents/teamwork_preview_challenger_r2_2/test_sandbox"
mkdir -p "$TEST_DIR"

# Source the exact Test 2.5 logic
run_test_2_5_audit() {
  local f_dirac="$1"
  local fidelity_failed=0
  local fidelity_errors=""

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

  # Step A: Mandatory active code tokens
  local stripped_code
  stripped_code=$(grep -v "^\s*--" "$f_dirac" | sed '/\/\*/,/\*\//d')
  for req_sym in "graphDirac" "chainComplex" "triangleComplex" "canonicalDigonComplex" "diracSquareCheck" "matTrace"; do
    if ! echo "$stripped_code" | grep -q "\<${req_sym}\>"; then
      fidelity_failed=$((fidelity_failed + 1))
      fidelity_errors="${fidelity_errors}\n- Missing required mathematical symbol in active code: '${req_sym}'"
    fi
  done

  # Step B: Per-theorem proposition signature verification
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

  # Step C: Negative anti-facade regex check
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

  echo "FAILURES=$fidelity_failed"
  if [ "$fidelity_failed" -gt 0 ]; then
    echo -e "ERRORS:$fidelity_errors"
    return 1
  else
    return 0
  fi
}

echo "=== TEST 0: Baseline Verification of clean DiracLaplacian.lean ==="
res0=$(run_test_2_5_audit "$TARGET_FILE" 2>&1) && code0=0 || code0=$?
echo "$res0"
if [ "$code0" -ne 0 ]; then
  echo "FATAL: Baseline check failed!"
  exit 1
fi
echo "[SUCCESS] Baseline passed clean with 0 errors."

echo -e "\n=== TEST 1: Perturbation - Tautological 0 = 0 on upper_right_zero ==="
cp "$TARGET_FILE" "$TEST_DIR/perturbed_tautology.lean"
sed -i '/theorem dirac_sq_upper_right_is_zero_chain/,/:= by/c\theorem dirac_sq_upper_right_is_zero_chain : 0 = 0 := by' "$TEST_DIR/perturbed_tautology.lean"
res1=$(run_test_2_5_audit "$TEST_DIR/perturbed_tautology.lean" 2>&1) && code1=0 || code1=$?
echo "$res1"
if [ "$code1" -ne 1 ]; then
  echo "FATAL: Perturbation 1 was NOT caught!"
  exit 1
fi
echo "[SUCCESS] Caught tautological 0=0 facade."

echo -e "\n=== TEST 2: Perturbation - Missing mandatory token matMul ==="
cp "$TARGET_FILE" "$TEST_DIR/perturbed_missing_token.lean"
sed -i 's/matMul D D/D/g' "$TEST_DIR/perturbed_missing_token.lean"
res2=$(run_test_2_5_audit "$TEST_DIR/perturbed_missing_token.lean" 2>&1) && code2=0 || code2=$?
echo "$res2"
if [ "$code2" -ne 1 ]; then
  echo "FATAL: Perturbation 2 was NOT caught!"
  exit 1
fi
echo "[SUCCESS] Caught missing operator token."

echo -e "\n=== TEST 3: Perturbation - Proof-irrelevance cheat ==="
cp "$TARGET_FILE" "$TEST_DIR/perturbed_proof_irrelevance.lean"
echo "theorem cheat : upper_right_zero = lower_left_zero := rfl" >> "$TEST_DIR/perturbed_proof_irrelevance.lean"
res3=$(run_test_2_5_audit "$TEST_DIR/perturbed_proof_irrelevance.lean" 2>&1) && code3=0 || code3=$?
echo "$res3"
if [ "$code3" -ne 1 ]; then
  echo "FATAL: Perturbation 3 was NOT caught!"
  exit 1
fi
echo "[SUCCESS] Caught proof-irrelevance facade pattern."

echo -e "\n=== TEST 4: Perturbation - Constant certificate literal equality ==="
cp "$TARGET_FILE" "$TEST_DIR/perturbed_cert_literal.lean"
echo "theorem cheat_cert : chainDiracSqCertificate = #[#[1]] := rfl" >> "$TEST_DIR/perturbed_cert_literal.lean"
res4=$(run_test_2_5_audit "$TEST_DIR/perturbed_cert_literal.lean" 2>&1) && code4=0 || code4=$?
echo "$res4"
if [ "$code4" -ne 1 ]; then
  echo "FATAL: Perturbation 4 was NOT caught!"
  exit 1
fi
echo "[SUCCESS] Caught constant certificate reflexive equality facade."

echo -e "\n=== TEST 5: Perturbation - Arithmetic substitution cheat ==="
cp "$TARGET_FILE" "$TEST_DIR/perturbed_arith.lean"
echo "theorem cheat_tr : trDsq = trΔ₀ + trDownΔ₁ := by rfl" >> "$TEST_DIR/perturbed_arith.lean"
res5=$(run_test_2_5_audit "$TEST_DIR/perturbed_arith.lean" 2>&1) && code5=0 || code5=$?
echo "$res5"
if [ "$code5" -ne 1 ]; then
  echo "FATAL: Perturbation 5 was NOT caught!"
  exit 1
fi
echo "[SUCCESS] Caught arithmetic substitution cheat."

echo -e "\nALL 5 ADVERSARIAL PERTURBATION CHALLENGES CAUGHT BY TEST 2.5!"
