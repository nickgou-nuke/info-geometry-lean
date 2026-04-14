# Translation Tracker (Tracked Handover Copy)

This tracked copy mirrors the operational tracker format for closure packets that must be promotable through PR flow.

| Packet ID | Seed Concept / Motif | Current Lock Status | Owner File | Lean Target | Obstruction / Notes |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `CP-002` | Relative modular KL scale/shape split | `formalized` | `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean` | `relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit` | Promoted to dedicated owner-level capstone surface; compiled with locked builds for `RelativeModularScaleShapeSplit`, `InfoGeometry.Canonical.All`, and `InfoGeometry.All`. |
| `CP-003` | Singular KAN/polar surrogate via Drazin/MP projector algebra | `formalized` | `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean` | `singular_decomposition_surrogate_package_of_commute` | Sandbox aliases removed after canonical transfer; package remains owner-backed by `GlobalChiralDecomposition` and `RelativeModularScaleShapeSplit`. |

## Runtime Note (2026-04-14)

- Build policy during active patching: file-level checks first (`lake env lean <file>`), no full-chain build after every patch.
- Local CP-002 maintenance status:
  - `lean/InfoGeometry/Canonical/RelativeModularBlockDiagonalCore.lean`: file-level compile OK.
  - `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean`: file-level compile OK (only linter warning at line 107: `simpa` → `simp` suggestion).
  - Legacy sandbox witness transferred; no sandbox module remains in canonical import graph.
- Local CP-003 bootstrap status:
  - Packet drafted at `handover/claim_packets/CP-003_singular_polar_surrogate.json`.
  - Canonical alias preserved at `InfoGeometry.Canonical.SingularDecompositionSurrogate.cp003_singular_polar_kan_package_of_commute`.
  - `lake build InfoGeometry.Canonical.All`: PASS after sandbox removal.
