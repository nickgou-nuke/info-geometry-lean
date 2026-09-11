import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.SplitOctonions.ProjectivePolarInvariant

Homogeneity-based projective incidence invariance.

This file proves the concrete algebraic facts needed for projective
split-octonion/twistor incidence:

* if a polar form is homogeneous in both arguments, then `B X Y = 0`
  is independent of nonzero scalar representatives;
* if a symmetry action preserves the polar form up to a nonzero scalar factor,
  then the incidence relation is invariant under that action;
* combining both gives the Erlangen statement:

  projective incidence is a symmetry invariant.

No wrappers.
No quotient construction.
No `sorry`.
-/

namespace InfoGeometry.Projective.SplitOctonions.ProjectivePolarInvariant

/--
Projective polar incidence is well-defined under independent nonzero scalar
rescaling of representatives.

If

  B(λ • X, Y) = λ * B(X,Y)

and

  B(X, μ • Y) = μ * B(X,Y),

then for nonzero `λ` and `μ`,

  B(X,Y)=0 ↔ B(λ • X, μ • Y)=0.
-/
theorem projective_incidence_well_defined
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_left :
      ∀ (l : R) (X Y : Carrier),
        polar (l • X) Y = l * polar X Y)
    (h_right :
      ∀ (m : R) (X Y : Carrier),
        polar X (m • Y) = m * polar X Y)
    (l m : R)
    (hl : l ≠ 0)
    (hm : m ≠ 0)
    (X Y : Carrier) :
    polar X Y = 0 ↔ polar (l • X) (m • Y) = 0 := by
  constructor
  · intro hXY
    rw [h_left l X (m • Y)]
    rw [h_right m X Y]
    rw [hXY]
    ring
  · intro hScaled
    rw [h_left l X (m • Y)] at hScaled
    rw [h_right m X Y] at hScaled
    have hInner : m * polar X Y = 0 := by
      rcases mul_eq_zero.mp hScaled with hl_zero | hrest
      · exact False.elim (hl hl_zero)
      · exact hrest
    rcases mul_eq_zero.mp hInner with hm_zero | hpolar
    · exact False.elim (hm hm_zero)
    · exact hpolar

/--
Forward-only form.

Zero polar incidence is preserved by arbitrary scalar rescaling. This direction
does not require nonzero scalars and does not require `NoZeroDivisors`.
-/
theorem projective_incidence_scaled_of_zero
    {R Carrier : Type*}
    [CommRing R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_left :
      ∀ (l : R) (X Y : Carrier),
        polar (l • X) Y = l * polar X Y)
    (h_right :
      ∀ (m : R) (X Y : Carrier),
        polar X (m • Y) = m * polar X Y)
    (l m : R)
    (X Y : Carrier)
    (hXY : polar X Y = 0) :
    polar (l • X) (m • Y) = 0 := by
  rw [h_left l X (m • Y)]
  rw [h_right m X Y]
  rw [hXY]
  ring

/--
Erlangen-style incidence invariance under a symmetry action.

If a symmetry action preserves the polar form up to a nonzero scalar factor,

  B(gX,gY) = χ(g) * B(X,Y),

then the zero-incidence relation is invariant:

  B(X,Y)=0 ↔ B(gX,gY)=0.
-/
theorem incidence_invariant_of_polar_scaled
    {R G Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    (polar : Carrier → Carrier → R)
    (act : G → Carrier → Carrier)
    (scale : G → R)
    (g : G)
    (hscale : scale g ≠ 0)
    (hcov :
      ∀ X Y : Carrier,
        polar (act g X) (act g Y) = scale g * polar X Y)
    (X Y : Carrier) :
    polar X Y = 0 ↔ polar (act g X) (act g Y) = 0 := by
  constructor
  · intro hXY
    rw [hcov X Y, hXY, mul_zero]
  · intro hAct
    rw [hcov X Y] at hAct
    rcases mul_eq_zero.mp hAct with hscale_zero | hpolar
    · exact False.elim (hscale hscale_zero)
    · exact hpolar

/--
Combined projective-plus-Erlangen incidence invariance.

If representatives are rescaled by nonzero scalars and then acted on by a
symmetry preserving the polar form up to a nonzero factor, incidence is
unchanged:

  B(X,Y)=0
    ↔
  B(g(λX), g(μY))=0.
-/
theorem projective_erlangen_incidence_invariant
    {R G Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_left :
      ∀ (l : R) (X Y : Carrier),
        polar (l • X) Y = l * polar X Y)
    (h_right :
      ∀ (m : R) (X Y : Carrier),
        polar X (m • Y) = m * polar X Y)
    (act : G → Carrier → Carrier)
    (scale : G → R)
    (g : G)
    (hscale : scale g ≠ 0)
    (hcov :
      ∀ X Y : Carrier,
        polar (act g X) (act g Y) = scale g * polar X Y)
    (l m : R)
    (hl : l ≠ 0)
    (hm : m ≠ 0)
    (X Y : Carrier) :
    polar X Y = 0
      ↔
    polar (act g (l • X)) (act g (m • Y)) = 0 := by
  have hProj :
      polar X Y = 0 ↔ polar (l • X) (m • Y) = 0 :=
    projective_incidence_well_defined
      polar h_left h_right l m hl hm X Y

  have hErl :
      polar (l • X) (m • Y) = 0
        ↔
      polar (act g (l • X)) (act g (m • Y)) = 0 :=
    incidence_invariant_of_polar_scaled
      polar act scale g hscale hcov (l • X) (m • Y)

  exact hProj.trans hErl

/--
Incidence fiber of a representative.

This is the set of all representatives incident with `X`.
-/
def incidenceFiber
    {R Carrier : Type*}
    [Zero R]
    (polar : Carrier → Carrier → R)
    (X : Carrier) : Set Carrier :=
  {Y : Carrier | polar X Y = 0}

/--
Scaling the first representative by a nonzero scalar does not change its
incidence fiber.
-/
theorem incidenceFiber_scale_left
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_left :
      ∀ (l : R) (X Y : Carrier),
        polar (l • X) Y = l * polar X Y)
    (l : R)
    (hl : l ≠ 0)
    (X : Carrier) :
    incidenceFiber polar (l • X) = incidenceFiber polar X := by
  ext Y
  constructor
  · intro hScaled
    change polar (l • X) Y = 0 at hScaled
    change polar X Y = 0
    rw [h_left l X Y] at hScaled
    rcases mul_eq_zero.mp hScaled with hl_zero | hpolar
    · exact False.elim (hl hl_zero)
    · exact hpolar
  · intro hXY
    change polar X Y = 0 at hXY
    change polar (l • X) Y = 0
    rw [h_left l X Y, hXY, mul_zero]

/--
Scaling the second representative by a nonzero scalar does not change
membership in an incidence fiber.
-/
theorem incidenceFiber_scale_right
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_right :
      ∀ (m : R) (X Y : Carrier),
        polar X (m • Y) = m * polar X Y)
    (m : R)
    (hm : m ≠ 0)
    (X Y : Carrier) :
    Y ∈ incidenceFiber polar X ↔
      m • Y ∈ incidenceFiber polar X := by
  constructor
  · intro hXY
    change polar X Y = 0 at hXY
    change polar X (m • Y) = 0
    rw [h_right m X Y, hXY, mul_zero]
  · intro hScaled
    change polar X (m • Y) = 0 at hScaled
    change polar X Y = 0
    rw [h_right m X Y] at hScaled
    rcases mul_eq_zero.mp hScaled with hm_zero | hpolar
    · exact False.elim (hm hm_zero)
    · exact hpolar

end InfoGeometry.Projective.SplitOctonions.ProjectivePolarInvariant
