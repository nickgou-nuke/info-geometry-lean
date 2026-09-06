import InfoGeometry.QuantumGeometry.Projective.Quotient

/-!
# Formal Projective Quotient Space P(H) = S(H)/U(1) Forwarding Module

Canonical owner: `InfoGeometry.QuantumGeometry.Projective.Quotient`

This module re-exports the canonical quotient construction:
- `U1Rel`: U(1) phase equivalence relation
- `projectiveSetoid`: Setoid structure on `NormalizedState H`
- `ProjectiveSpace H`: Quotient space ℙ(H) = S(H)/U(1)
- `toProjective`: Projection π : S(H) → ℙ(H)
- Descended tensors: `QGT_projective`, `fubiniStudyMetric_projective`, `berryCurvature_projective`
- Universal geometric bounds on ℙ(H): `QGT_cauchy_schwarz_projective`, `robertson_schrodinger_qgt_bound_projective`
-/
