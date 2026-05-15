# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:51.538140+00:00`
Root: `lean/InfoGeometry/Krein/HestenesCPTONNDualityBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **12**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesCPTONNDualityBridge.lean` | `advisory` | 30 | 0 | 12 | 6 | 18 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesCPTONNDualityBridge.lean`
- module: `InfoGeometry.Krein.HestenesCPTONNDualityBridge`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L68 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.arithmetic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.theta_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.theta_krein_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.theta_fixes_omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.theta_phaseAxis_flip` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.theta_volumeState_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.theta_maps_hurwitzRoots` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.onn_volumeState_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.onn_maps_hurwitzRoots` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.onn_duality_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field HestenesCPTONNDualityBridge.cpt_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L135 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L216 [advisory] `bridge-shaped-declaration` in `theorem onn_duality_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L222 [advisory] `bridge-shaped-declaration` in `theorem cpt_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

