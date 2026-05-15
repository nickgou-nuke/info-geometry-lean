# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:55.503898+00:00`
Root: `lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **16**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean` | `advisory` | 34 | 0 | 16 | 2 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean`
- module: `InfoGeometry.Canonical.SingularBoundaryCorrection`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field RayGaugeData.quotientMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field RayGaugeData.weylAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field RayGaugeData.radialPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field RayGaugeData.quotientPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.dilation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.dilation_eq_half_sub_mp_projectors` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.spectralProjector_star` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.regularRadialTransportCloses` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.closure_of_zero_boundaryGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.gradedSurvivor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field SingularBoundaryCorrection.boundaryGenerator_skew_adjoints_to_krein_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [soft] `skeletal-proof` in `theorem boundaryGenerator_eq_projector_commutator` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem rightBoundaryGenerator_eq_projector_commutator` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem boundaryScale_eq_projectorObstruction_norm` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem boundaryGenerator_eq_zero_iff_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L175 [soft] `skeletal-proof` in `theorem boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero` — proof appears to close via minimal tactic one-liner

