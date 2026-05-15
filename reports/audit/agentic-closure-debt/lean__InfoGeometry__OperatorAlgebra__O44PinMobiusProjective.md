# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:19.453265+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **57**
- Hard: **0**
- Soft: **48**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean` | `advisory` | 105 | 0 | 48 | 9 | 57 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`
- module: `InfoGeometry.OperatorAlgebra.O44PinMobiusProjective`
- status: `advisory`
- debt_score: `105`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `law-field-locker` in `structure-field SplitQuadratic44.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field SplitQuadratic44.polar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field SplitQuadratic44.q_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field SplitQuadratic44.polar_symm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field SplitQuadratic44.nondegenerate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field SplitQuadratic44.signature44` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [advisory] `existential-packaging` in `def SameRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L126 [advisory] `existential-packaging` in `def SameProjectiveRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L210 [soft] `law-field-locker` in `structure-field Orthogonal44.preserves_q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field Pin44CoverDatum.isPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [soft] `law-field-locker` in `structure-field Pin44CoverDatum.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field Pin44CoverDatum.cover` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field Pin44CoverDatum.odd_reflection_socket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `law-field-locker` in `structure-field Pin44CoverDatum.even_spin_subcover_socket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L316 [soft] `law-field-locker` in `structure-field PinChiralityActionDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L319 [soft] `law-field-locker` in `structure-field PinChiralityActionDatum.actionOnChi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field PinChiralityActionDatum.even_preserves_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L328 [soft] `law-field-locker` in `structure-field PinChiralityActionDatum.odd_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L375 [soft] `law-field-locker` in `structure-field SplitQuadratic55.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field SplitQuadratic55.polar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L377 [soft] `law-field-locker` in `structure-field SplitQuadratic55.q_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [soft] `law-field-locker` in `structure-field SplitQuadratic55.polar_symm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [soft] `law-field-locker` in `structure-field SplitQuadratic55.nondegenerate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L385 [soft] `law-field-locker` in `structure-field SplitQuadratic55.signature55` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [soft] `law-field-locker` in `structure-field Orthogonal55.preserves_q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L413 [advisory] `existential-packaging` in `def SameRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L592 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.embed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L595 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.embed_is_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L599 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.projectivePoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L602 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.projectivePoint_vec_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L609 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.inversion_realizes_sphere_inversion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L612 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.base_orthogonal_lift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L616 [soft] `law-field-locker` in `structure-field ConformalMobius44Extension.full_mobius_generation_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L626 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L663 [soft] `simp-law-injection` in `simp-declaration baseSplitQuadratic44_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L667 [soft] `simp-law-injection` in `simp-declaration ambientSplitQuadratic55_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L671 [soft] `simp-law-injection` in `simp-declaration baseToAmbient_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L676 [soft] `simp-law-injection` in `simp-declaration liftBaseOrthogonal_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L741 [soft] `law-field-locker` in `structure-field Pin55CoverDatum.isPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L742 [soft] `law-field-locker` in `structure-field Pin55CoverDatum.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L743 [soft] `law-field-locker` in `structure-field Pin55CoverDatum.cover` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L750 [soft] `law-field-locker` in `structure-field Pin55CoverDatum.inversion_is_reflection_or_null_swap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L766 [soft] `law-field-locker` in `structure-field PinMobiusProjective44.basePin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L767 [soft] `law-field-locker` in `structure-field PinMobiusProjective44.conformalPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L768 [soft] `law-field-locker` in `structure-field PinMobiusProjective44.basePin_lifts_to_conformalPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L771 [soft] `law-field-locker` in `structure-field PinMobiusProjective44.acts_on_projective_null_rays` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L774 [soft] `law-field-locker` in `structure-field PinMobiusProjective44.reflection_and_chiral_classification_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L785 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L813 [soft] `law-field-locker` in `structure-field O44PinMobiusProjectiveConstructionData.basePin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L814 [soft] `law-field-locker` in `structure-field O44PinMobiusProjectiveConstructionData.conformalPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L815 [soft] `law-field-locker` in `structure-field O44PinMobiusProjectiveConstructionData.basePin_lifts_to_conformalPin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L816 [soft] `law-field-locker` in `structure-field O44PinMobiusProjectiveConstructionData.acts_on_projective_null_rays` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L817 [soft] `law-field-locker` in `structure-field O44PinMobiusProjectiveConstructionData.reflection_and_chiral_classification_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L826 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L841 [advisory] `existential-packaging` in `def O44PinMobiusProjectiveCompatibility` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L849 [advisory] `existential-packaging` in `def O44PinMobiusProjectiveOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

