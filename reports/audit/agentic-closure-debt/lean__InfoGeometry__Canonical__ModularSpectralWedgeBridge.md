# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:30.313033+00:00`
Root: `lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **9**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean` | `advisory` | 22 | 0 | 9 | 4 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean`
- module: `InfoGeometry.Canonical.ModularSpectralWedgeBridge`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [soft] `law-field-locker` in `structure-field IsCompatibleWedge.epsilon_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field IsCompatibleWedge.pzero_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `skeletal-proof` in `theorem owned_epsilon_mul_P_D_eq_zero` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem P_D_mul_owned_epsilon_eq_zero` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `law-field-locker` in `structure-field WedgeCalibrated.flow_commutes_owned_P_D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field WedgeCalibrated.flow_commutes_owned_epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `skeletal-proof` in `theorem flow_commutes_wedgeSign` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem flow_commutes_pzero` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem flow_mul_activeProjector_eq_activeProjector_mul_flow` — proof appears to close via minimal tactic one-liner
  - L132 [advisory] `local-hypothesis-injection` in `theorem flow_mul_activeProjector_eq_activeProjector_mul_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

