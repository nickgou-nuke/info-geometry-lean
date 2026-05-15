# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:46.395937+00:00`
Root: `lean/InfoGeometry/Thermo/BuresWassersteinKMSCost.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **18**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/BuresWassersteinKMSCost.lean` | `advisory` | 42 | 0 | 18 | 6 | 24 |

## Findings by file

### `lean/InfoGeometry/Thermo/BuresWassersteinKMSCost.lean`
- module: `InfoGeometry.Thermo.BuresWassersteinKMSCost`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `simp-law-injection` in `simp-declaration coe_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `theorem coe_mk` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.dist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.squaredDist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.dist_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.squaredDist_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.dist_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.squaredDist_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field BuresWassersteinDatum.bures_wasserstein_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L156 [soft] `law-field-locker` in `structure-field KMSHolonomyTransport.transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field KMSHolonomyTransport.preserves_domain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field KMSHolonomyTransport.kms_origin_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field KMSHolonomyTransport.holonomy_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L242 [advisory] `local-hypothesis-injection` in `theorem holonomyCost_eq_zero_of_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L262 [soft] `law-field-locker` in `structure-field BuresDetailedBalanceBridge.DetailedBalanced` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [soft] `law-field-locker` in `structure-field BuresDetailedBalanceBridge.detailed_balance_implies_zero_cost` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field BuresDetailedBalanceBridge.zero_cost_implies_detailed_balance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L321 [soft] `law-field-locker` in `structure-field BilingualKMSHolonomyCompatibility.bilingual_stokes_holonomy_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L328 [soft] `law-field-locker` in `structure-field BilingualKMSHolonomyCompatibility.thermal_cylinder_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

