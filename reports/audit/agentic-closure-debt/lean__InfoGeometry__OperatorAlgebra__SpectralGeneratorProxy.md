# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:22.311067+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **20**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean` | `advisory` | 49 | 0 | 20 | 9 | 29 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean`
- module: `InfoGeometry.OperatorAlgebra.SpectralGeneratorProxy`
- status: `advisory`
- debt_score: `49`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `skeletal-proof` in `theorem self` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L151 [soft] `law-field-locker` in `structure-field PhaseResolventDatum.denom_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field PhaseResolventDatum.denom_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L229 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.bounded_transform_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L264 [soft] `law-field-locker` in `structure-field BoundedRealRepresentation.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L266 [soft] `law-field-locker` in `structure-field BoundedRealRepresentation.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field BoundedRealRepresentation.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [soft] `law-field-locker` in `structure-field BoundedRealRepresentation.map_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L275 [soft] `law-field-locker` in `structure-field BoundedRealRepresentation.map_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L306 [soft] `simp-law-injection` in `simp-declaration endCommutator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L324 [soft] `law-field-locker` in `structure-field AdjointBackend.adj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L325 [soft] `law-field-locker` in `structure-field AdjointBackend.adjoint_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field CompactDefectBackend.IsCompactLike` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L341 [soft] `law-field-locker` in `structure-field CompactDefectBackend.add_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field CompactDefectBackend.neg_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L361 [soft] `skeletal-proof` in `theorem sub_mem` — proof appears to close via minimal tactic one-liner
  - L398 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.rep_phase_linear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.commutator_defect_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L426 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.kasparov_cycle_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L441 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L480 [advisory] `existential-packaging` in `def PhaseResolventOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L492 [advisory] `existential-packaging` in `def BoundedTransformOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L499 [advisory] `existential-packaging` in `def BoundedKasparovCycleOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

