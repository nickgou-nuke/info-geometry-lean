# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:13.132267+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **53**
- Hard: **0**
- Soft: **43**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean` | `advisory` | 96 | 0 | 43 | 10 | 53 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/DrazinProjectionLocalization.lean`
- module: `InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization`
- status: `advisory`
- debt_score: `96`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field SelfAdjointIdempotentPair.support_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field SelfAdjointIdempotentPair.residue_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field SelfAdjointIdempotentPair.support_residue_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field SelfAdjointIdempotentPair.residue_support_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field SelfAdjointIdempotentPair.support_add_residue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field SelfAdjointIdempotentPair.selfAdjointLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L46 [soft] `law-field-locker` in `structure-field DrazinInverseData.element_mul_inverse_eq_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field DrazinInverseData.inverse_mul_element_eq_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field DrazinInverseData.commutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field DrazinInverseData.inverse_element_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.element` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.element_mul_inverse_eq_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.inverse_mul_element_eq_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.commutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field FiberwiseDrazinData.inverse_element_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L147 [soft] `law-field-locker` in `structure-field DrazinFiberEquivalence.fiberEquiv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L176 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.element_eq_regular_add_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.regular_supported_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.regular_supported_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.nilpotent_residue_supported_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.nilpotent_residue_supported_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.coreInv_supported_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.coreInv_supported_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.regular_mul_coreInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.coreInv_mul_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.nilpotent_mul_coreInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.coreInv_mul_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field RelativeCoreNilpotentDecomposition.nilpotentResidueLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L275 [soft] `simp-law-injection` in `simp-declaration toDrazinInverseData_element` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L277 [soft] `skeletal-proof` in `theorem toDrazinInverseData_element` — proof appears to close via minimal tactic one-liner
  - L280 [soft] `simp-law-injection` in `simp-declaration toDrazinInverseData_inverse` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L282 [soft] `skeletal-proof` in `theorem toDrazinInverseData_inverse` — proof appears to close via minimal tactic one-liner
  - L293 [soft] `law-field-locker` in `structure-field DivisionResidueBlockPacket.simpleResidueLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L308 [soft] `law-field-locker` in `structure-field FrobeniusSelfDualPacket.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L309 [soft] `law-field-locker` in `structure-field FrobeniusSelfDualPacket.pairing_mul_left_eq_pairing_mul_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [soft] `law-field-locker` in `structure-field FrobeniusSelfDualPacket.nondegeneracyLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L317 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L328 [soft] `law-field-locker` in `structure-field SpectralDivisorStratification.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [soft] `law-field-locker` in `structure-field SpectralDivisorStratification.drazinAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L330 [soft] `law-field-locker` in `structure-field SpectralDivisorStratification.drazin_weight_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [soft] `law-field-locker` in `structure-field SpectralDivisorStratification.locusCoverLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L360 [soft] `law-field-locker` in `structure-field TwoProjectionDrazinLocalizationPacket.localizationLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L366 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

