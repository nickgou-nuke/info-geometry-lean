# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:52.170328+00:00`
Root: `lean/InfoGeometry/Krein/HestenesKreinNaturalConeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **21**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesKreinNaturalConeBridge.lean` | `advisory` | 50 | 0 | 21 | 8 | 29 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesKreinNaturalConeBridge.lean`
- module: `InfoGeometry.Krein.HestenesKreinNaturalConeBridge`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.coneVector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.coneVector_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.eval_eq_krein_vector_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.J_fixes_cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeBridge.naturalCone_self_dual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L63 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L69 [advisory] `bridge-shaped-declaration` in `theorem eval_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L77 [advisory] `bridge-shaped-declaration` in `theorem coneVector_mem_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L106 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeVacuum.natural` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeVacuum.Omega_normalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeVacuum.J_fixes_Omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeVacuum.cyclic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeVacuum.separating` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L132 [soft] `section-law-variable` in `variable V` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L150 [advisory] `bridge-shaped-declaration` in `theorem Omega_normalized_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L169 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeKMSBridge.vacuum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeKMSBridge.coneVector_eq_Omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [soft] `law-field-locker` in `structure-field HestenesKreinNaturalConeKMSBridge.complexEval_eq_realConeEval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L195 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L244 [soft] `law-field-locker` in `structure-field KreinIsometricVectorFlow.vectorFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L246 [soft] `law-field-locker` in `structure-field KreinIsometricVectorFlow.vectorFlow_kreinIsometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L252 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L252 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

