# Project: Global Codebase Refactor & CAS O(1) Optimization

## Architecture
- **CAS Computation & Certificate Generation**: Python/SymPy/Sage scripts compute exact polynomial, block-matrix, and projector identities externally, emitting deterministic mathematical certificates.
- **Lean 4 Structural & Definitional Equality Verification**: Target Lean files import or define certificate structures verified by kernel $O(1)$ definitional equality (`rfl`) or direct term unifications (`exact`), eliminating brute-force search tactics (`native_decide`, `simpa using`, `decide`, `simp` storms).
- **Categorical Inductive Colimit & Homotopy Alignment**: In accordance with `TensorTowerColimit.lean` and `ChiralDirectedGraphHomotopy.lean`, all limits and equivalences are established via direct inductive colimits and explicit 2-cell homotopy witnesses without unverified VM escapes or non-algebraic continuations.
- **Sequential Build Locking**: All verification passes execute sequentially under `/tmp/info-geometry-build.lock` via `tools/infra/run_locked_lake_build.py`.
- **Subagent Sandbox Isolation**: All modifications must be generated and verified in `.agents/sandbox_<target>/` before any live promotion.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | CAS Dirac Laplacian Certificate Generator | Python CAS script computing exact $D, D^2, \Delta_0, \partial_1 \partial_1^T, \mathrm{Tr}(D^2)$ certificates | M1 | ORIGINAL_REQUEST §R2 |
| 2 | Dirac Laplacian O(1) Proof Replacement | Eliminate all 10 `native_decide` in `lean/DAG/DiracLaplacian.lean` via CAS certificates and $O(1)$ proofs | M1 | ORIGINAL_REQUEST §R1, §R3 |
| 3 | Re-enable DiracLaplacian in DAG Module | Restore `import DAG.DiracLaplacian` in `lean/DAG.lean` and ensure clean compilation | M1 | ORIGINAL_REQUEST Acceptance |
| 4 | Noncommutative Fock Bridge O(1) Replacement | Replace 5 `simpa using` chains with `exact` in `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean` | M2 | ORIGINAL_REQUEST §R1, §R3 |
| 5 | CAS Fock Projector Idempotence Certificate | Attach CAS Clifford projector certificate ($P_\pm^2 = P_\pm$, $P_+ P_- = 0$) | M2 | ORIGINAL_REQUEST §R2 |
| 6 | E2E Test Suite & Build Verification | Verify target files compile with locked lake build, no warnings, zero `native_decide` / `simpa using` | M3 | ORIGINAL_REQUEST Acceptance |
| 7 | Victory Audit & Handoff | Conduct integrity audit and deliver comprehensive report to Sentinel for independent victory audit | M4 | ORIGINAL_REQUEST Acceptance |
| 8 | Surgical Refactoring of Moore-Penrose Bottleneck | Eliminate all 26 `native_decide` in `lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean` via CAS certificates and O(1) proofs | M5 | 2026-09-22T03:53:52Z Mandate |
| 9 | Final Independent Victory Audit 3 | Full independent forensic, axiomatic, and E2E verification confirming unconditional victory | M5 | 2026-09-22T03:53:52Z Mandate |
| 10 | DAG Dominators O(1) Refactor | Eliminate 3 `native_decide` in `lean/DAG/Dominators.lean` via O(1) kernel evaluation, purging all `native_decide` from `DAG.lean` | M6 | 2026-09-22T05:17:23Z Mandate |
| 11 | Campbell-Meyer Weak Drazin CAS O(1) Refactor | Eliminate 22 `native_decide` in `CampbellMeyerWeakDrazin.lean` via SymPy integer scaling and structural unit conjugation | M7 | 2026-09-22T05:17:23Z Mandate |
| 12 | Promotion, E2E Test Suite & Test 2.5 Verification | Promote verified sandbox files to live repo, run locked build and E2E suite | M8 | 2026-09-22T05:17:23Z Mandate |
| 13 | Final Victory Audit 4 & Sentinel Report | Independent forensic integrity audit across all promoted targets | M8 | 2026-09-22T05:17:23Z Mandate |
| 14 | FieldCorrelatorProjection Discovery & Compression | Phase 0 discovery, OpenGauss /golf & /refactor, CAS O(1) certificates in sandbox for FieldCorrelatorProjection | M9 | 2026-09-22T12:06:12Z Mandate |
| 15 | KreinAttentionEnergy Compression | OpenGauss /golf & /refactor, CAS O(1) certificates in sandbox for KreinAttentionEnergy | M10 | 2026-09-22T12:06:12Z Mandate |
| 16 | ConnesHodgeBridge Compression | OpenGauss /golf & /refactor, CAS O(1) certificates in sandbox for ConnesHodgeBridge | M11 | 2026-09-22T12:06:12Z Mandate |
| 17 | 5-Agent Gate Panel & Sentinel Report | Reviewers, Challengers, Auditor gate verification, promotion, and report to Sentinel | M12 | 2026-09-22T12:06:12Z Mandate |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| 1 | M1: Dirac Laplacian CAS & O(1) Refactor | `scripts/cas_dirac_laplacian_certificate.py`, `lean/DAG/DiracLaplacian.lean`, `lean/DAG.lean` | none | DONE |
| 2 | M2: Noncommutative Fock Bridge O(1) Refactor | `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean` | none | DONE |
| 3 | M3: E2E Verification & Test Suite | Full target compilation via `run_locked_lake_build.py`, tactic elimination verification | M1, M2 | DONE |
| 4 | M4: Final Victory Audit 2 & Sentinel Reporting | Forensic integrity audit & victory reporting to Sentinel | M3 | DONE |
| 5 | M5: Surgical Compression Swarm & Victory Audit 3 | Surgical elimination of 26 `native_decide` bottlenecks in `Hartwig1976SVDMoorePenroseBorder.lean` & final victory audit | M4 | DONE |
| 6 | M6: DAG Dominators O(1) Refactor | `lean/DAG/Dominators.lean` (3 `native_decide` -> 0) | M5 | DONE |
| 7 | M7: Campbell-Meyer Weak Drazin CAS O(1) Refactor | `lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` (22 `native_decide` -> 0) | M6 | DONE |
| 8 | M8: Global Verification & Victory Audit 4 | E2E suite verification, Test 2.5 proposition fidelity, independent Victory Auditor | M6, M7 | DONE (VICTORY) |
| 9 | M9: FieldCorrelatorProjection Compression | `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` sandbox compression & 5-agent Gate Panel | M8 | DONE (PROMOTED) |
| 10 | M10: KreinAttentionEnergy Compression | `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean` sandbox compression & 5-agent Gate Panel | M9 | DONE (PROMOTED) |
| 11 | M11: ConnesHodgeBridge Compression | `lean/DAG/ConnesHodgeBridge.lean` sandbox compression | M10 | DONE (PROMOTED) |
| 12 | M12: 5-Agent Gate Panel & Sentinel Report | Final global promotion, E2E suite verification, and report to Sentinel | M9, M10, M11 | DONE (VICTORY) |

## Code Layout
- `scripts/cas_dirac_laplacian_certificate.py`: CAS certificate generator script for Dirac Laplacian.
- `.agents/sandbox_correlator/`: Sandbox environment for FieldCorrelatorProjection compression (M9, promoted).
- `.agents/sandbox_krein/`: Sandbox environment for KreinAttentionEnergy compression (M10, promoted).
- `.agents/sandbox_connes_hodge/`: Sandbox environment for ConnesHodgeBridge compression (M11).
- `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`: Target bottleneck 1 (compressed, 0 tactics, live).
- `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`: Target bottleneck 2 (compressed, 0 tactics, live promoted).
- `lean/DAG/ConnesHodgeBridge.lean`: Target bottleneck 3 (compressed, 0 tactics, live promoted).
- `tools/infra/run_locked_lake_build.py`: Shared lock compilation wrapper.
