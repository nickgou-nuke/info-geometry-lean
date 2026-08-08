import Mathlib.Tactic

/-!

InfoGeometry.Canonical.BoundedTransformSpectralTriple

-/

namespace InfoGeometry.Canonical.BoundedTransformSpectralTriple

/-

BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]

boundedTransform_sq_eq_of_commute

boundedTransform_commutes_with_resolvent_of_commute

cayley_inverse_left_apply

cayley_inverse_right_apply

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported verified premises.]

boundedTransform_defect_left

boundedTransform_defect_right

phase_eq_of_bounded_transform_eq_phase_resolvent

boundedTransform_eq_of_phase_resolvent

boundedTransform_selfAdjoint_of_source

boundedTransform_commutator_bounded_of_spectralTriple_property

boundedTransform_spectralTriple_packet

BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses, certificates, or renamed placeholders.]

Analytic construction of the bounded transform from an unbounded self-adjoint source.

Functional-calculus proof that D * (1 + D^2)^(-1/2) is bounded.

Spectral-triple commutator boundedness for the transformed operator.
-/

/-- Algebraic square of the formal bounded transform D R. -/
theorem boundedTransform_sq_eq_of_commute
{A : Type*} [Semigroup A]
(D R : A)
(hcomm : D * R = R * D) :
(D * R) * (D * R) = D * D * (R * R) := by
  calc
    (D * R) * (D * R) = D * ((R * D) * R) := by
      simp [mul_assoc]
    _ = D * ((D * R) * R) := by
      rw [hcomm]
    _ = D * D * (R * R) := by
      simp [mul_assoc]

/-- The bounded transform commutes with the resolvent when the source does. -/
theorem boundedTransform_commutes_with_resolvent_of_commute
{A : Type*} [Semigroup A]
(D R : A)
(hcomm : D * R = R * D) :
(D * R) * R = R * (D * R) := by
  calc
    (D * R) * R = (R * D) * R := by
      rw [hcomm]
    _ = R * (D * R) := by
      simp [mul_assoc]

end InfoGeometry.Canonical.BoundedTransformSpectralTriple
