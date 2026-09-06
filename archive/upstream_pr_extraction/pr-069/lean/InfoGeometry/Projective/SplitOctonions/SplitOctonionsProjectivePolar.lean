import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar

Projective polar incidence under independent unit rescaling.

This file proves the basic algebraic fact:

  `polar X Y = 0 ↔ polar ((λ : R) • X) ((μ : R) • Y) = 0`

for projective unit scalars `λ μ : Rˣ`.

No new projective quotient, no new incidence structure, no wrapper.
-/

namespace InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar

/--
Projective orthogonality is well-defined under independent unit rescaling.

This is the abstract algebraic kernel behind local polar incidence on
projective Zorn rays.
-/
theorem projective_incidence_well_defined_units
    {R Carrier : Type*}
    [CommRing R]
    [AddCommGroup Carrier] [Module R Carrier]
    (splitOctPolar : Carrier → Carrier → R)
    (h_left :
      ∀ (l0 : R) (X Y : Carrier),
        splitOctPolar (l0 • X) Y = l0 * splitOctPolar X Y)
    (h_right :
      ∀ (m0 : R) (X Y : Carrier),
        splitOctPolar X (m0 • Y) = m0 * splitOctPolar X Y)
    (l m : Rˣ) (X Y : Carrier) :
    splitOctPolar X Y = 0
      ↔
    splitOctPolar ((l : R) • X) ((m : R) • Y) = 0 := by
  constructor
  · intro h
    rw [h_left (l : R) X ((m : R) • Y)]
    rw [h_right (m : R) X Y]
    rw [h]
    simp
  · intro h
    rw [h_left (l : R) X ((m : R) • Y)] at h
    rw [h_right (m : R) X Y] at h

    have h_strip_left :
        (m : R) * splitOctPolar X Y = 0 := by
      have h' :=
        congrArg (fun t : R => ((l⁻¹ : Rˣ) : R) * t) h
      simpa [mul_assoc] using h'

    have h_strip_right :
        splitOctPolar X Y = 0 := by
      have h' :=
        congrArg (fun t : R => ((m⁻¹ : Rˣ) : R) * t) h_strip_left
      simpa [mul_assoc] using h'

    exact h_strip_right

/--
Right-facing form for downstream rewriting.

This is just the symmetric orientation of
`projective_incidence_well_defined_units`.
-/
theorem projective_incidence_well_defined_units_right
    {R Carrier : Type*}
    [CommRing R]
    [AddCommGroup Carrier] [Module R Carrier]
    (splitOctPolar : Carrier → Carrier → R)
    (h_left :
      ∀ (l0 : R) (X Y : Carrier),
        splitOctPolar (l0 • X) Y = l0 * splitOctPolar X Y)
    (h_right :
      ∀ (m0 : R) (X Y : Carrier),
        splitOctPolar X (m0 • Y) = m0 * splitOctPolar X Y)
    (l m : Rˣ) (X Y : Carrier) :
    splitOctPolar ((l : R) • X) ((m : R) • Y) = 0
      ↔
    splitOctPolar X Y = 0 := by
  exact
    (projective_incidence_well_defined_units
      splitOctPolar h_left h_right l m X Y).symm

end InfoGeometry.Projective.SplitOctonions.SplitOctonionsProjectivePolar
