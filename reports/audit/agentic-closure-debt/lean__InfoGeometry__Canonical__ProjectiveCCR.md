# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:44.706996+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectiveCCR.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **6**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectiveCCR.lean` | `advisory` | 15 | 0 | 6 | 3 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectiveCCR.lean`
- module: `InfoGeometry.Canonical.ProjectiveCCR`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [soft] `law-field-locker` in `structure-field ProjectiveBoundaryPacket.split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `law-field-locker` in `structure-field ProjectiveBoundaryPacket.vacuumMode_eq_one_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field ProjectiveBoundaryPacket.regulatedHeatKernel_eq_subtract_one_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field ProjectiveBoundaryPacket.superKMS_detailed_balance_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `skeletal-proof` in `theorem drazinCore_eq_kernel` — proof appears to close via minimal tactic one-liner
  - L51 [soft] `skeletal-proof` in `theorem excitedStateSector_eq_orthogonal` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `bridge-shaped-declaration` in `theorem projective_boundary_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

