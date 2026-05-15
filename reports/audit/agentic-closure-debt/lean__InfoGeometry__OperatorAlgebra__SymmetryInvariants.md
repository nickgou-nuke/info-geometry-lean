# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:24.306486+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **75**
- Hard: **0**
- Soft: **61**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean` | `advisory` | 136 | 0 | 61 | 14 | 75 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean`
- module: `InfoGeometry.OperatorAlgebra.SymmetryInvariants`
- status: `advisory`
- debt_score: `136`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `law-field-locker` in `structure-field SymmetryAction.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field SymmetryAction.act_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field SymmetryAction.act_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L56 [soft] `simp-law-injection` in `simp-declaration act_one_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration act_mul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration act_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `skeletal-proof` in `theorem act_zero` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `simp-law-injection` in `simp-declaration act_one_ring` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `theorem act_one_ring` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `simp-law-injection` in `simp-declaration act_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `skeletal-proof` in `theorem act_add` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `simp-law-injection` in `simp-declaration act_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `skeletal-proof` in `theorem act_neg` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `simp-law-injection` in `simp-declaration act_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `skeletal-proof` in `theorem act_sub` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `simp-law-injection` in `simp-declaration act_mul_op` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `skeletal-proof` in `theorem act_mul_op` — proof appears to close via minimal tactic one-liner
  - L150 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L180 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `simp-law-injection` in `simp-declaration mem_invariantSubring_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L266 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L267 [soft] `skeletal-proof` in `theorem one_isProjector` — proof appears to close via minimal tactic one-liner
  - L271 [soft] `skeletal-proof` in `theorem zero_isProjector` — proof appears to close via minimal tactic one-liner
  - L329 [advisory] `local-hypothesis-injection` in `theorem supported_image_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L384 [soft] `law-field-locker` in `structure-field ComplementaryProjectors.sum_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L387 [soft] `law-field-locker` in `structure-field ComplementaryProjectors.pq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L390 [soft] `law-field-locker` in `structure-field ComplementaryProjectors.qp_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L501 [soft] `law-field-locker` in `structure-field InvariantPredicate.pred` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field InvariantPredicate.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L519 [soft] `law-field-locker` in `structure-field InvariantReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L520 [soft] `law-field-locker` in `structure-field InvariantReadout.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L535 [soft] `law-field-locker` in `structure-field InvariantPairing.pair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L536 [soft] `law-field-locker` in `structure-field InvariantPairing.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L552 [soft] `law-field-locker` in `structure-field CovariantReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L553 [soft] `law-field-locker` in `structure-field CovariantReadout.covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L570 [soft] `law-field-locker` in `structure-field DefectLocus.locus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L571 [soft] `law-field-locker` in `structure-field DefectLocus.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L586 [soft] `law-field-locker` in `structure-field ProjectorSupportedDefect.supported` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L651 [advisory] `existential-packaging` in `def SymmetryInvariantOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L671 [advisory] `existential-packaging` in `def InvariantProjectorOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L702 [soft] `law-field-locker` in `structure-field OperatorSymmetryAction.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L704 [soft] `law-field-locker` in `structure-field OperatorSymmetryAction.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L708 [soft] `law-field-locker` in `structure-field OperatorSymmetryAction.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L713 [soft] `law-field-locker` in `structure-field OperatorSymmetryAction.act_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L717 [soft] `law-field-locker` in `structure-field OperatorSymmetryAction.act_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L744 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L746 [soft] `simp-law-injection` in `simp-declaration act_one_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L758 [soft] `simp-law-injection` in `simp-declaration act_map_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L760 [soft] `skeletal-proof` in `theorem act_map_zero` — proof appears to close via minimal tactic one-liner
  - L770 [soft] `simp-law-injection` in `simp-declaration act_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L800 [soft] `simp-law-injection` in `simp-declaration mem_invariantSubmodule_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L895 [soft] `simp-law-injection` in `simp-declaration commutator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L896 [soft] `skeletal-proof` in `theorem commutator_self` — proof appears to close via minimal tactic one-liner
  - L922 [soft] `law-field-locker` in `structure-field InvariantProjectorPair.regular_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L925 [soft] `law-field-locker` in `structure-field InvariantProjectorPair.defect_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L928 [soft] `law-field-locker` in `structure-field InvariantProjectorPair.projector_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L931 [soft] `law-field-locker` in `structure-field InvariantProjectorPair.regular_defect_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L934 [soft] `law-field-locker` in `structure-field InvariantProjectorPair.defect_regular_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L948 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1010 [soft] `law-field-locker` in `structure-field EquivariantLinearMap.toLinearMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1011 [soft] `law-field-locker` in `structure-field EquivariantLinearMap.equivariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1024 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1042 [soft] `law-field-locker` in `structure-field EquivariantAlgebraMap.toLinearMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1043 [soft] `law-field-locker` in `structure-field EquivariantAlgebraMap.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1046 [soft] `law-field-locker` in `structure-field EquivariantAlgebraMap.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1051 [soft] `law-field-locker` in `structure-field EquivariantAlgebraMap.equivariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1064 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1111 [soft] `law-field-locker` in `structure-field InvariantReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1112 [soft] `law-field-locker` in `structure-field InvariantReadout.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1339 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1370 [advisory] `existential-packaging` in `def GeometricOriginOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1397 [soft] `law-field-locker` in `structure-field OperatorGeometryOrigin.has_projector_geometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1405 [advisory] `existential-packaging` in `def HasInvariantOperatorOrigin` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

