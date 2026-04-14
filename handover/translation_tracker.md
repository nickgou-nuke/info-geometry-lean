# Translation Tracker (Tracked Handover Copy)

This tracked copy mirrors the operational tracker format for closure packets that must be promotable through PR flow.

| Packet ID | Seed Concept / Motif | Current Lock Status | Owner File | Lean Target | Obstruction / Notes |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `CP-002` | Relative modular KL scale/shape split | `formalized` | `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean` | `relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit` | Promoted to dedicated owner-level capstone surface; compiled with locked builds for `RelativeModularScaleShapeSplit`, `InfoGeometry.Canonical.All`, and `InfoGeometry.All`. |

## Runtime Note (2026-04-14)

- Build policy during active patching: file-level checks first (`lake env lean <file>`), no full-chain build after every patch.
- Local CP-002 maintenance status:
  - `lean/InfoGeometry/Canonical/RelativeModularBlockDiagonalCore.lean`: file-level compile OK.
  - `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean`: file-level compile OK (only linter warning at line 107: `simpa` → `simp` suggestion).
  - `lean/InfoGeometry/Canonical/Sandbox_CP002_Lifted.lean`: file-level compile OK after replacing brittle rewrite flow with projector-orthogonality proof.
  - Witness memo preserved at `handover/witnesses/CP-002_sandbox_witness.md` (non-authority sandbox surface).
