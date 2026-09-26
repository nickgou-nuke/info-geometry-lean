# Test Suite Readiness: CAS O(1) Optimization Project

## 1. Status & Location
- **Status**: READY FOR AUDIT & EXECUTION (15/15 TESTS VERIFIED PASSING)
- **Runner Path**: `/home/goutev/info-geometry-lean/tools/e2e_cas_o1_suite.sh`
- **Permissions**: Executable (`chmod +x tools/e2e_cas_o1_suite.sh`)
- **Documentation**: `/home/goutev/info-geometry-lean/TEST_INFRA.md`
- **Milestone Scope**: Milestone 3 (E2E Verification & Test Suite)

---

## 2. Verification Capabilities (The 4 Tiers, 15 Tests)

The E2E Test Suite comprehensively verifies the CAS O(1) optimization across 4 distinct tiers:

| Tier | Name | Target / Focus | Verification Method |
| :--- | :--- | :--- | :--- |
| **Tier 1** | Feature Coverage (3 tests) | `DAG.DiracLaplacian`, `InfoGeometry.Quantum.NoncommutativeFockBridge` | Locked Lake build (`tools/infra/run_locked_lake_build.py`) verifying clean compilation (exit code 0) |
| **Tier 2** | Boundary & Corner Cases (5 tests) | Brute-force elimination (`native_decide`, `simpa using`), proof completeness (`sorry`/`admit`), parameter handling, and **Test 2.5: Proposition Fidelity & Anti-Facade Audit** | Static & AST token analysis auditing: 0 `native_decide`, 0 `simpa using`, 0 `sorry`/`admit`, mandatory combinatorial graph operands, and active ban on facade patterns |
| **Tier 3** | CAS & Integration Verification (4 tests) | `scripts/cas_dirac_laplacian_certificate.py` & `lean/DAG.lean` | Python execution of CAS certificate generator verifying polynomial block decomposition ($D^2 = \Delta_0 \oplus \Delta_1^{\text{down}}$), trace conservation, active `import DAG.DiracLaplacian` in `lean/DAG.lean`, and full DAG module compilation |
| **Tier 4** | Compilation Performance & O(1) Verification (3 tests) | Elaboration speed & timeout enforcement | Strict timeout limit ($\le 15\text{s}$) kernel evaluation testing, proving O(1) definitional checking without CPU hangs; build lock hygiene |

---

## 3. How to Run the Tests

### Option A: Complete E2E Test Suite (All 4 Tiers, 15 Tests)
```bash
cd /home/goutev/info-geometry-lean
./tools/e2e_cas_o1_suite.sh --tier all
```

### Option B: Selective Tier Execution
```bash
# Tier 1 only (Feature Coverage)
./tools/e2e_cas_o1_suite.sh --tier 1

# Tier 2 only (Boundary & Corner Cases, including Test 2.5 Anti-Facade Audit)
./tools/e2e_cas_o1_suite.sh --tier 2

# Tier 3 only (CAS & Integration Verification)
./tools/e2e_cas_o1_suite.sh --tier 3

# Tier 4 only (Compilation Performance & O(1) Verification)
./tools/e2e_cas_o1_suite.sh --tier 4
```

---

## 4. Pass / Fail Acceptance Criteria

A test run is considered passing (`exit code 0`) if and only if:
1. `DAG.DiracLaplacian` and `InfoGeometry.Quantum.NoncommutativeFockBridge` compile with 0 warnings/errors under `run_locked_lake_build.py`.
2. Static audit verifies strictly **0** occurrences of `native_decide` in `lean/DAG/DiracLaplacian.lean`.
3. Static audit verifies strictly **0** occurrences of `simpa using` in `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`.
4. Static audit verifies strictly **0** occurrences of `sorry` or `admit` across target files.
5. Anti-facade audit (Test 2.5) verifies 100% proposition fidelity against git HEAD and rejects all tautological dummy patterns.
6. CAS certificate script (`scripts/cas_dirac_laplacian_certificate.py`) runs with exit code 0 and verifies matrix certificates for `chain`, `triangle`, and `digon` complexes.
7. `lean/DAG.lean` contains active `import DAG.DiracLaplacian` and compiles under locked build with 0 errors.
8. Kernel compilation time for both target files completes within $\le 15$ seconds without timing out.

---

## 5. Auditor Verification Checklist

The independent victory auditor (`teamwork_preview_auditor` / `sentinel`) should execute:
```bash
# 1. Run full E2E test suite (15/15 tests must pass)
./tools/e2e_cas_o1_suite.sh --tier all

# 2. Check exit code
echo "Exit code: $?"

# 3. Confirm zero native_decide
grep -n "native_decide" lean/DAG/DiracLaplacian.lean || echo "VERIFIED: Zero native_decide"

# 4. Confirm zero simpa using
grep -n "simpa using" lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean || echo "VERIFIED: Zero simpa using"

# 5. Confirm CAS script execution
python3 scripts/cas_dirac_laplacian_certificate.py
```
