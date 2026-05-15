# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:13.278631+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **19**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean` | `advisory` | 43 | 0 | 19 | 5 | 24 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean`
- module: `InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field DrazinProjectorPair.Pcore_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field DrazinProjectorPair.Pnil_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field DrazinProjectorPair.projector_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field DrazinProjectorPair.core_nil_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field DrazinProjectorPair.nil_core_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L176 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplit.coreRep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplit.splitRep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplit.core_no_square_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplit.defect_maps_to_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplit.defect_supported_by_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplit.core_supported_by_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L291 [soft] `law-field-locker` in `structure-field MetricDrazinProjectorPair.drazin_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field MetricDrazinProjectorPair.metric_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L337 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplitCompatibility.coreRep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplitCompatibility.splitRep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplitCompatibility.core_no_square_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L356 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplitCompatibility.defect_maps_to_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L362 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplitCompatibility.defect_supported_by_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L368 [soft] `law-field-locker` in `structure-field DrazinRepresentedSplitCompatibility.core_supported_by_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L393 [advisory] `existential-packaging` in `def DrazinRepresentedSplitOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

