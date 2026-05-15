# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:36.913446+00:00`
Root: `lean/InfoGeometry/Geometry/DualFlat.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **33**
- Hard: **0**
- Soft: **24**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/DualFlat.lean` | `advisory` | 57 | 0 | 24 | 9 | 33 |

## Findings by file

### `lean/InfoGeometry/Geometry/DualFlat.lean`
- module: `InfoGeometry.Geometry.DualFlat`
- status: `advisory`
- debt_score: `57`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `simp-law-injection` in `simp-declaration divergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration eGeodesic_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `lemma eGeodesic_zero` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `simp-law-injection` in `simp-declaration eGeodesic_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `skeletal-proof` in `lemma eGeodesic_one` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `skeletal-proof` in `lemma ConvexOn.eGeodesicConvex` — proof appears to close via minimal tactic one-liner
  - L87 [advisory] `local-hypothesis-injection` in `lemma ConvexOn.eGeodesicConvex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `local-hypothesis-injection` in `lemma ConvexOn.eGeodesicConvex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [soft] `skeletal-proof` in `lemma eGeodesicConvex.convexOn_univ` — proof appears to close via minimal tactic one-liner
  - L99 [advisory] `local-hypothesis-injection` in `lemma eGeodesicConvex.convexOn_univ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [soft] `law-field-locker` in `structure-field GradientBijection.invDual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field GradientBijection.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field GradientBijection.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `simp-law-injection` in `simp-declaration mGeodesic_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `skeletal-proof` in `lemma mGeodesic_zero` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `simp-law-injection` in `simp-declaration mGeodesic_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L143 [soft] `skeletal-proof` in `lemma mGeodesic_one` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `skeletal-proof` in `lemma dualCoord_mGeodesic` — proof appears to close via minimal tactic one-liner
  - L169 [advisory] `local-hypothesis-injection` in `lemma divergence_three_point` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L219 [soft] `simp-law-injection` in `simp-declaration divergenceVec_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L232 [soft] `skeletal-proof` in `lemma divergenceVec_three_point` — proof appears to close via minimal tactic one-liner
  - L276 [soft] `law-field-locker` in `structure-field HessianManifold.twiceDiff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field HilbertHessian.twiceDiff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L349 [soft] `simp-law-injection` in `simp-declaration divergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L353 [soft] `skeletal-proof` in `theorem three_point_identity` — proof appears to close via minimal tactic one-liner
  - L365 [advisory] `local-hypothesis-injection` in `theorem three_point_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L391 [soft] `skeletal-proof` in `lemma dualCoord_apply_sub_eq_deriv_mul` — proof appears to close via minimal tactic one-liner
  - L426 [soft] `law-field-locker` in `structure-field UnnormalizedMeasure.mass_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L436 [soft] `skeletal-proof` in `lemma projectiveDivergence_eq_kl` — proof appears to close via minimal tactic one-liner
  - L465 [advisory] `existential-packaging` in `theorem bayesian_update_pythagorean` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L480 [advisory] `existential-packaging` in `theorem bayesian_update_pythagorean_bregman` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

