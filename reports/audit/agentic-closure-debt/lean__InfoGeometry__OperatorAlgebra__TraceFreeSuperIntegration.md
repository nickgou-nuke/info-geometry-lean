# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:25.682766+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/TraceFreeSuperIntegration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **44**
- Hard: **0**
- Soft: **33**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/TraceFreeSuperIntegration.lean` | `advisory` | 77 | 0 | 33 | 11 | 44 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/TraceFreeSuperIntegration.lean`
- module: `InfoGeometry.OperatorAlgebra.TraceFreeSuperIntegration`
- status: `advisory`
- debt_score: `77`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L70 [soft] `law-field-locker` in `structure-field GradingDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L86 [soft] `simp-law-injection` in `simp-declaration gradeLeft_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `skeletal-proof` in `theorem gradeLeft_one` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `law-field-locker` in `structure-field SuperIntegrationDatum.backendReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field SuperIntegrationDatum.superReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field SuperIntegrationDatum.superReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field SuperIntegrationDatum.graded_cyclicity_or_kms_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L171 [soft] `law-field-locker` in `structure-field ModularWeightBackend.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field ModularWeightBackend.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field ModularWeightBackend.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field ModularWeightBackend.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [soft] `law-field-locker` in `structure-field ModularWeightBackend.kms_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L215 [soft] `law-field-locker` in `structure-field ModularSuperWeightDatum.superWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field ModularSuperWeightDatum.modular_super_kms_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L254 [soft] `law-field-locker` in `structure-field CoreSuperTraceDatum.embed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [soft] `law-field-locker` in `structure-field CoreSuperTraceDatum.coreReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field CoreSuperTraceDatum.superReadoutOfBase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [soft] `law-field-locker` in `structure-field CoreSuperTraceDatum.superReadoutOfBase_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field CoreSuperTraceDatum.core_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L282 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L311 [soft] `law-field-locker` in `structure-field DixmierSuperTraceDatum.dixmierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [soft] `law-field-locker` in `structure-field DixmierSuperTraceDatum.superDixmierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field DixmierSuperTraceDatum.superDixmierReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [soft] `law-field-locker` in `structure-field DixmierSuperTraceDatum.logarithmic_divergence_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L326 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L347 [soft] `law-field-locker` in `structure-field ZetaSuperTraceDatum.zeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field ZetaSuperTraceDatum.superResidue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field ZetaSuperTraceDatum.superFinitePart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L353 [soft] `law-field-locker` in `structure-field ZetaSuperTraceDatum.zeta_super_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L376 [soft] `law-field-locker` in `structure-field CyclicSuperCocycleDatum.cocycleReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L378 [soft] `law-field-locker` in `structure-field CyclicSuperCocycleDatum.superCocycleReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [soft] `law-field-locker` in `structure-field CyclicSuperCocycleDatum.superCocycleReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L384 [soft] `law-field-locker` in `structure-field CyclicSuperCocycleDatum.cyclic_cocycle_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L428 [soft] `law-field-locker` in `structure-field TypeIIISuperIntegrationDatum.typeIII_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L435 [soft] `law-field-locker` in `structure-field TypeIIISuperIntegrationDatum.no_bare_trace_on_base_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L461 [advisory] `existential-packaging` in `def TraceFreeSuperIntegrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

