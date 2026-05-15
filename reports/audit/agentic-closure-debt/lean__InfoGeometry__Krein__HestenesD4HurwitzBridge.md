# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:51.798624+00:00`
Root: `lean/InfoGeometry/Krein/HestenesD4HurwitzBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **36**
- Hard: **0**
- Soft: **22**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesD4HurwitzBridge.lean` | `advisory` | 58 | 0 | 22 | 14 | 36 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesD4HurwitzBridge.lean`
- module: `InfoGeometry.Krein.HestenesD4HurwitzBridge`
- status: `advisory`
- debt_score: `58`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L48 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L72 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.hurwitzRoots` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.discreteMoebiusAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.d4_hurwitz_root_system` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.hurwitz_maximal_order` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.d4_self_dual_lattice` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.discrete_moebius_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.triality_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.affine_kac_moody_closure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field D4LatticeKacMoodyBridge.affine_central_charge_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L132 [advisory] `bridge-shaped-declaration` in `theorem d4_hurwitz_root_system_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L138 [advisory] `bridge-shaped-declaration` in `theorem hurwitz_maximal_order_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L150 [advisory] `bridge-shaped-declaration` in `theorem discrete_moebius_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L156 [advisory] `bridge-shaped-declaration` in `theorem triality_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L162 [advisory] `bridge-shaped-declaration` in `theorem affine_kac_moody_closure_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L184 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.moebius` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.hurwitzRoot` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.root_eq_wignerJonesAtom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.affineNullRootPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.affineNullRootMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.affineNullRootPlus_eq_uPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.affineNullRootMinus_eq_uMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.d4_hurwitz_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.d4_self_dual_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.triality_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.affine_kac_moody_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field D4HurwitzArithmeticBridge.affineCentralCharge_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L245 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L245 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L262 [advisory] `bridge-shaped-declaration` in `theorem triality_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L268 [advisory] `bridge-shaped-declaration` in `theorem affine_kac_moody_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L308 [advisory] `bridge-shaped-declaration` in `theorem affineNullRootPlus_eq_uPlus_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L314 [advisory] `bridge-shaped-declaration` in `theorem affineNullRootMinus_eq_uMinus_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

