# Test Infrastructure: CAS O(1) Optimization Project

## 1. Architectural Overview

The CAS O(1) Optimization Project replaces computationally intensive brute-force search tactics (`native_decide`, `simpa using`, unguided `simp` storms) across target Lean 4 modules with exact mathematical Computer Algebra System (CAS) certificates and kernel-level $O(1)$ definitional equality (`rfl`) or term unification (`exact`).

To verify that these optimizations maintain complete mathematical correctness, eliminate compiler bottlenecks, and avoid regressions, the test infrastructure is organized into a deterministic, multi-tiered End-to-End (E2E) Test Suite executed via:
```bash
tools/e2e_cas_o1_suite.sh
```

All test execution complies with the repository commandments defined in `AGENTS.md`:
- **Sequential Build Locking**: All Lake builds are routed through `tools/infra/run_locked_lake_build.py --wait-for-build-lock` to serialize access to the Lean compiler and prevent race conditions on `.lake/build`.
- **Cache Preservation**: Destructive cache operations (`lake clean`, `rm -rf .lake/build`) are strictly prohibited.
- **Bash-Only Tooling**: Tests and verification pipelines are strictly managed via bash runners, bypassing interactive prompt barriers.
- **Strict Anti-Facade & Integrity Mandate**: Tests execute genuine compiler, CAS, and static analysis commands without dummy mocks or hardcoded falsifications.

---

## 2. 4-Tier Verification Hierarchy

The test runner `tools/e2e_cas_o1_suite.sh` implements a 4-tier verification pipeline:

### Tier 1: Feature Coverage (Locked Lake Builds)
- **Objective**: Validate that both primary target modules compile successfully in the Lean 4.28.1 environment under the repository build lock.
- **Target 1**: `DAG.DiracLaplacian` (`lean/DAG/DiracLaplacian.lean`)
  - Command: `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG.DiracLaplacian`
  - Success Criterion: Exit code 0, clean compiler termination, valid olean artifact generation.
- **Target 2**: `InfoGeometry.Quantum.NoncommutativeFockBridge` (`lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`)
  - Command: `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Quantum.NoncommutativeFockBridge`
  - Success Criterion: Exit code 0, clean compiler termination.
- **Structural Integrity**: Confirms both source files exist, contain non-trivial declaration content (> 10 lines), and define valid module namespace boundaries.

### Tier 2: Boundary & Corner Cases (Brute-Force Elimination & Proof Completeness)
- **Objective**: Ensure that the target files contain zero brute-force tactics and zero unproven gaps (`sorry` / `admit`).
- **Test 2.1 (`native_decide` Elimination)**:
  - Audits `lean/DAG/DiracLaplacian.lean` for any occurrence of `native_decide`.
  - In the unoptimized state, 10 occurrences existed.
  - Requirement: Strictly 0 occurrences.
- **Test 2.2 (`simpa using` Elimination)**:
  - Audits `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean` for any occurrence of `simpa using`.
  - In the unoptimized state, 5 occurrences existed.
  - Requirement: Strictly 0 occurrences.
- **Test 2.3 (Proof Completeness & Rigor)**:
  - Audits both files for incomplete proof placeholders (`\b(sorry|admit)\b`).
  - Requirement: Strictly 0 occurrences.
- **Test 2.4 (Boundary Parameter & Error Resilience)**:
  - Validates that the CAS certificate generator script executes cleanly and handles edge/boundary parameters without unhandled exceptions.

### Tier 3: CAS & Integration Verification
- **Objective**: Verify mathematical agreement between external CAS certificates and Lean modules, and confirm top-level module integration.
- **Test 3.1 (Python CAS Certificate Oracle)**:
  - Executes `python3 scripts/cas_dirac_laplacian_certificate.py`.
  - Verifies exit code 0.
  - Confirms output certifies:
    1. `canonicalChainComplex`
    2. `canonicalTriangleComplex`
    3. `canonicalDigonComplex`
    4. Block-diagonal decomposition: $D^2 = \Delta_0 \oplus \Delta_1^{\text{down}}$
    5. Trace conservation law: $\mathrm{Tr}(D^2) = \mathrm{Tr}(\Delta_0) + \mathrm{Tr}(\partial_1 \partial_1^T)$.
- **Test 3.2 (Export Wiring in `lean/DAG.lean`)**:
  - Validates that `lean/DAG.lean` contains an active, uncommented `import DAG.DiracLaplacian`.
- **Test 3.3 (DAG Aggregate Module Build)**:
  - Executes `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG`.
  - Ensures no cyclic imports, unresolved symbols, or module breakages in downstream consumers.

### Tier 4: Compilation Performance & O(1) Verification
- **Objective**: Empirically prove that the refactored proofs achieve $O(1)$ definitional equality checking without CPU hangs or exponential elaboration blowups.
- **Test 4.1 (`DAG.DiracLaplacian` Kernel Benchmark)**:
  - Compiles `lean/DAG/DiracLaplacian.lean` under an explicit 20-second timeout.
  - Measures wall-clock execution time.
  - Enforces a strict $O(1)$ threshold ($\le 15$ seconds, including full Mathlib environment load).
- **Test 4.2 (`NoncommutativeFockBridge` Elaboration Benchmark)**:
  - Compiles `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean` under an explicit 20-second timeout.
  - Enforces a strict $O(1)$ threshold ($\le 15$ seconds).
- **Test 4.3 (Concurrency & Lock Hygiene)**:
  - Verifies that `/tmp/info-geometry-build.lock` is properly released.
  - Confirms no orphaned or zombie compiler processes are left running.

---

## 3. Authoritative Mathematical Oracles

| Identity | Mathematical Formula | Oracle Source | Lean Verification |
| :--- | :--- | :--- | :--- |
| **Dirac Square Block Decomposition** | $D^2 = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \Delta_1^{\text{down}} \end{pmatrix}$ | `scripts/cas_dirac_laplacian_certificate.py` (SymPy) | `DAG.DiracLaplacian.dirac_squared_block_diagonal_*` via `rfl` / CAS certificates |
| **Dirac Square Trace Identity** | $\mathrm{Tr}(D^2) = \mathrm{Tr}(\Delta_0) + \mathrm{Tr}(\partial_1 \partial_1^T)$ | `scripts/cas_dirac_laplacian_certificate.py` (SymPy) | `DAG.DiracLaplacian.trace_D_sq_equals_trace_laplacians_chain` |
| **Dirac Nilpotency Check** | $\mathrm{diracSquareCheck}(K) = \mathrm{true}$ | Exact graph Dirac formula | `DAG.dirac_square_check_*` via `rfl` |
| **Fock Projector Idempotence** | $P_\pm^2 = P_\pm,\; P_+ P_- = 0$ | `tools/gap/clifford_braiding_center.g`, `tools/infra/galgebra_clifford_peirce.py` | `InfoGeometry.Quantum.NoncommutativeFockBridge` via `exact` |
| **Majorana CAR Witness** | $\{\gamma(u), \gamma(v)\} = 2\langle u, v\rangle I$ | Clifford algebraic relations | `RealMajoranaDatum.car_realization_of_clifford` via `exact` |

---

## 4. Execution Commands

### Run Complete Suite (All Tiers)
```bash
./tools/e2e_cas_o1_suite.sh
```

### Run Individual Tiers
```bash
# Tier 1: Feature Coverage only
./tools/e2e_cas_o1_suite.sh --tier 1

# Tier 2: Boundary & Corner Cases only
./tools/e2e_cas_o1_suite.sh --tier 2

# Tier 3: CAS & Integration Verification only
./tools/e2e_cas_o1_suite.sh --tier 3

# Tier 4: Compilation Performance & O(1) Verification only
./tools/e2e_cas_o1_suite.sh --tier 4
```

### Verbose Mode
```bash
./tools/e2e_cas_o1_suite.sh --verbose
```

---

## 5. Exit Code & Reporting Contract

- **Exit Code 0**: All executed tests passed successfully across all selected tiers.
- **Exit Code 1**: One or more assertions failed. Detailed error descriptions, file paths, line numbers, and command outputs are printed to stdout/stderr.
