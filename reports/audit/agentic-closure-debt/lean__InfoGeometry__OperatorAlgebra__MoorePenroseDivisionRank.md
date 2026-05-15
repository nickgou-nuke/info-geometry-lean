# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:18.885249+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/MoorePenroseDivisionRank.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **17**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/MoorePenroseDivisionRank.lean` | `advisory` | 41 | 0 | 17 | 7 | 24 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/MoorePenroseDivisionRank.lean`
- module: `InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank`
- status: `advisory`
- debt_score: `41`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field MoorePenroseVolumeCalibration.mpProjector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field MoorePenroseVolumeCalibration.trace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field MoorePenroseVolumeCalibration.projectorLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field MoorePenroseVolumeCalibration.projectorLaw_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field MoorePenroseVolumeCalibration.volume_eq_mp_trace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L76 [advisory] `local-hypothesis-injection` in `theorem entropy_nonneg_of_one_le_mp_trace` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L90 [soft] `law-field-locker` in `structure-field FaithfulDivisionTraceLaw.trace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field FaithfulDivisionTraceLaw.isDivisionAlgebraFiber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field FaithfulDivisionTraceLaw.representedNontrivially` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field FaithfulDivisionTraceLaw.identityOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field FaithfulDivisionTraceLaw.trace_identity_ge_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L131 [soft] `law-field-locker` in `structure-field MoorePenroseDivisionIdentityLaw.faithfulTrace_trace_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field MoorePenroseDivisionIdentityLaw.mpProjector_eq_identity_of_division` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L182 [soft] `law-field-locker` in `structure-field DivisionAlgebraFiberRankCertificate.isDivisionAlgebraFiber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field DivisionAlgebraFiberRankCertificate.representedNontrivially` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field DivisionAlgebraFiberRankCertificate.trace_ge_one_of_division` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L228 [soft] `law-field-locker` in `structure-field DivisionAlgebraFiberLemma.isDivisionAlgebraFiber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L230 [soft] `law-field-locker` in `structure-field DivisionAlgebraFiberLemma.trace_ge_one_of_division` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

