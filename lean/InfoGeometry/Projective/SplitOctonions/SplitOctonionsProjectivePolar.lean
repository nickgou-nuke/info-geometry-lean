import Mathlib

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar

Projective orthogonality is invariant under nonzero rescaling of representatives.
-/

namespace InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar

/--
Projective orthogonality well-definedness.

If a split-octonion polar form is homogeneous in each argument, then
`splitOctPolar X Y = 0` is invariant under independent nonzero scalar rescaling
of `X` and `Y`.
-/
theorem projective_incidence_well_defined
    {R : Type*} [CommRing R] [IsDomain R]
    {Carrier : Type*} [AddCommGroup Carrier] [Module R Carrier]
    (splitOctPolar : Carrier → Carrier → R)
    (h_left :
      ∀ (l : R) (X Y : Carrier),
        splitOctPolar (l • X) Y = l * splitOctPolar X Y)
    (h_right :
      ∀ (m : R) (X Y : Carrier),
        splitOctPolar X (m • Y) = m * splitOctPolar X Y)
    (l m : R) (hl : l ≠ 0) (hm : m ≠ 0) (X Y : Carrier) :
    splitOctPolar X Y = 0 ↔ splitOctPolar (l • X) (m • Y) = 0 := by
  constructor
  · intro h
    rw [h_left, h_right, h, mul_zero, mul_zero]
  · intro h
    rw [h_left, h_right] at h
    have h_inner : m * splitOctPolar X Y = 0 :=
      (mul_eq_zero.mp h).resolve_left hl
    exact (mul_eq_zero.mp h_inner).resolve_left hm

end InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar
