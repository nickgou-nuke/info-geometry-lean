# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:12.865847+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/DrazinEntropyFunctional.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **37**
- Hard: **0**
- Soft: **28**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/DrazinEntropyFunctional.lean` | `advisory` | 65 | 0 | 28 | 9 | 37 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/DrazinEntropyFunctional.lean`
- module: `InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional`
- status: `advisory`
- debt_score: `65`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field DrazinStableReadout.elementOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field DrazinStableReadout.regularPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field DrazinStableReadout.nilpotentResidue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field DrazinStableReadout.drazinInverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field DrazinStableReadout.stableVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field DrazinStableReadout.valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field DrazinStableReadout.stableVolume_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field DrazinStableReadout.decompositionLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field DrazinStableReadout.drazinLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field DrazinStableReadout.decomposition_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field DrazinStableReadout.drazin_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field AlgebraicDrazinStableReadout.drazinDataOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field AlgebraicDrazinStableReadout.drazinData_element_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field AlgebraicDrazinStableReadout.drazinData_inverse_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L155 [soft] `law-field-locker` in `structure-field DrazinEntropyFunctional.kB_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field DrazinEntropyFunctional.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field DrazinEntropyFunctional.entropy_eq_kB_log_stableVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L190 [advisory] `existential-packaging` in `structure FiniteDrazinMicrostateCalibration` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L201 [soft] `law-field-locker` in `structure-field FiniteDrazinMicrostateCalibration.microstatesOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [soft] `law-field-locker` in `structure-field FiniteDrazinMicrostateCalibration.stableVolume_eq_card` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field FiniteDrazinMicrostateCalibration.microstates_nonempty` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L233 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L235 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L250 [soft] `law-field-locker` in `structure-field DrazinGWVolumeCalibration.gwVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [soft] `law-field-locker` in `structure-field DrazinGWVolumeCalibration.gwVolume_eq_stableVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L283 [soft] `law-field-locker` in `structure-field DrazinInformationExtractionPacket.stableInformation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field DrazinInformationExtractionPacket.singularResidue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [soft] `law-field-locker` in `structure-field DrazinInformationExtractionPacket.stableInformationLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L286 [soft] `law-field-locker` in `structure-field DrazinInformationExtractionPacket.singularResidueLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field DrazinInformationExtractionPacket.stableInformation_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [soft] `law-field-locker` in `structure-field DrazinInformationExtractionPacket.singularResidue_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

