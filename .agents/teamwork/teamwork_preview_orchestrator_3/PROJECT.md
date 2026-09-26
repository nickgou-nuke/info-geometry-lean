# Project: OpenGauss Lean 4 Build Repair

## Architecture
- Modules: `InfoGeometry.BottPeriodicityReconciliation`, `InfoGeometryCore.Basic`, `DAG.SearchCoreTests`, `DAG.HodgeTheorems`.
- Goal: Fix build errors under QMS strict enforcement, ensuring mathematical fidelity and kernel-verified proofs.

## Feature Inventory
| # | Target | Description | Milestone | Source | Status |
|---|--------|-------------|-----------|--------|--------|
| 1 | `InfoGeometry.BottPeriodicityReconciliation` | Fix missing `sigma1R`, `sigma3R` and `ring_nf` tactic failure | M1 | Survey | IN_PROGRESS |
| 2 | `DAG.SearchCoreTests` | Re-verify manual fixes / status | M2 | Survey | VERIFIED_PASS (RC=0) |
| 3 | `DAG.HodgeTheorems` | Re-verify manual fixes / status | M3 | Survey | VERIFIED_PASS (RC=0) |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| 1 | Sandbox Repair of Bott Periodicity | Implement O(1) certificate in `.agents/sandbox_bott/` | Phase 0 Discovery | IN_PROGRESS |
| 2 | Verification of DAG.SearchCoreTests | Locked lake build check | none | DONE |
| 3 | Verification of DAG.HodgeTheorems | Locked lake build check | none | DONE |
| 4 | Gate Panel Verification | Reviewers, Challengers, Forensic Auditor on Sandbox | M1 | PENDING |
| 5 | Live Repo Promotion & Global Check | Promote verified file, run locked build | M4 | PENDING |

## Code Layout
- Live Owner Files:
  - `lean/InfoGeometry/BottPeriodicityReconciliation.lean`
  - `lib/InfoGeometryCore/InfoGeometryCore/Basic.lean`
  - `lean/DAG/SearchCoreTests.lean`
  - `lean/DAG/HodgeTheorems.lean`
- Sandbox Environment:
  - `.agents/sandbox_bott/BottPeriodicityReconciliation.lean`
  - `.agents/sandbox_bott/Basic_addition.lean`

## Interface Contracts
- `sigma1R : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]`
- `sigma3R : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]`
- `cl11_generator_relations`: `sigma1 * sigma1 = I2 ∧ epsilon * epsilon = -I2 ∧ sigma1 * epsilon + epsilon * sigma1 = 0`
- `cl11_basis_spans_M2`: `∀ A : Matrix (Fin 2) (Fin 2) ℝ, ∃ a b c d : ℝ, A = a • I2 + b • sigma1 + c • epsilon + d • sigma3`
- `bott_trifactor_capstone`: Genuine proof term `⟨cl11_generator_relations, cl11_basis_spans_M2⟩`
