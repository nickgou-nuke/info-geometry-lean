# Master Execution Plan: orchestrator_6

Target: `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean` (24 `native_decide` calls)

## Phase 1: Exploration & Mathematical Strategy
- **Step 1.1**: Dispatch 3 parallel Explorers:
  - `explorer_bracket_1`: Analyze definitions of `nativeCommutator`, `nativeAnticommutator`, `modularSigmaPlus`, `modularSigmaMinus`, `modularNPlus`, `modularNMinus`, and investigate why `native_decide` was used and how `decide` or `rfl` or CAS reduction behaves.
  - `explorer_bracket_2`: Analyze dependency graph and downstream importers (`RiemannSurprisalFluxAudit`, `SplitOctonionSixSectorBridge`) to ensure zero API breakage and 100% proposition fidelity.
  - `explorer_bracket_3`: Explore the algebraic basis table in `InfoGeometry.Algebra.Zorn.ThreeColorNativeBracketTable` and determine whether direct definitional reduction / integer coordinate evaluation can be mirrored or adapted.
- **Step 1.2**: Synthesize Explorer reports into `exploration_summary.md`.

## Phase 2: Worker Sandbox Implementation
- **Step 2.1**: Initialize isolated sandbox `.agents/sandbox_three_color_bracket/`.
- **Step 2.2**: Dispatch Worker to refactor `ThreeColorNativeBracketTable.lean` in the sandbox:
  - Eliminate all 24 `native_decide` blocks.
  - Prove all commutators and anticommutators using pure kernel reduction (`decide`, `rfl`, or structural algebraic lemmas).
  - Verify clean compilation under build lock (`python3 tools/infra/run_locked_lake_build.py`).
  - Verify 0 `sorry`, 0 `Lean.ofReduceBool`, 100% proposition fidelity.

## Phase 3: Review, Adversarial Challenge & Forensic Audit
- **Step 3.1**: Dispatch 2 Reviewers independently to verify code quality, proof rigor, and build output.
- **Step 3.2**: Dispatch 2 Challengers to perform adversarial mutation testing (modifying signs, basis vectors, coefficients) to confirm kernel rejection of invalid propositions.
- **Step 3.3**: Dispatch Forensic Auditor to check for forbidden tokens, VM reflection escapes, and axiom hygiene (`#print axioms`).
- **Step 3.4**: Gate evaluation in `GATE_STATUS.md`.

## Phase 4: Promotion & Global E2E Verification
- **Step 4.1**: Promote verified sandbox file to `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean`.
- **Step 4.2**: Run locked lake build of target and downstream importers.
- **Step 4.3**: Run authoritative E2E test suite `./tools/e2e_cas_o1_suite.sh --tier all`.
- **Step 4.4**: Update `PROJECT.md` milestones and feature inventory.

## Phase 5: Final Victory Audit & Sentinel Reporting
- **Step 5.1**: Dispatch independent Victory Auditor (`victory_auditor_6`).
- **Step 5.2**: Generate final handoff report and notify Sentinel.
