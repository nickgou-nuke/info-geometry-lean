import InfoGeometry.Projective.SplitOctonions.ProjectivePolarInvariant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiber

Incidence fibers for projective/Erlangen polar geometry.

This file proves set-level consequences of representative incidence
representative incidence invariance:

* rescaling one representative does not change its incidence fiber;
* an Erlangen symmetry sends the incidence fiber of `Y` to the incidence
  fiber of `g Y`.

No new structures.
No quotient construction.
No wrappers.
No `sorry`.
-/

namespace InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiber

/--
Left representative rescaling does not change the incidence fiber.
-/
theorem incidenceFiber_scale_left
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_left :
      ∀ (lam : R) (X Y : Carrier),
        polar (lam • X) Y = lam * polar X Y)
    (lam : R) (hlam : lam ≠ 0)
    (X : Carrier) :
    {Y : Carrier | polar (lam • X) Y = 0}
      =
    {Y : Carrier | polar X Y = 0} := by
  ext Y
  change (polar (lam • X) Y = 0 ↔ polar X Y = 0)
  rw [h_left lam X Y]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hlam
  · intro h
    rw [h, mul_zero]

/--
Right representative rescaling does not change the incidence fiber.
-/
theorem incidenceFiber_scale_right
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_right :
      ∀ (μ : R) (X Y : Carrier),
        polar X (μ • Y) = μ * polar X Y)
    (μ : R) (hμ : μ ≠ 0)
    (Y : Carrier) :
    {X : Carrier | polar X (μ • Y) = 0}
      =
    {X : Carrier | polar X Y = 0} := by
  ext X
  change (polar X (μ • Y) = 0 ↔ polar X Y = 0)
  rw [h_right μ X Y]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hμ
  · intro h
    rw [h, mul_zero]

/--
Erlangen covariance preserves incidence fibers in preimage form.
-/
theorem incidenceFiber_erlangen_preimage
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    (polar : Carrier → Carrier → R)
    (g : Carrier ≃ Carrier)
    (χ : R)
    (hχ : χ ≠ 0)
    (hcov :
      ∀ X Y : Carrier,
        polar (g X) (g Y) = χ * polar X Y)
    (Y : Carrier) :
    {X : Carrier | polar (g X) (g Y) = 0}
      =
    {X : Carrier | polar X Y = 0} := by
  ext X
  change (polar (g X) (g Y) = 0 ↔ polar X Y = 0)
  rw [hcov X Y]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hχ
  · intro h
    rw [h, mul_zero]

/--
Erlangen covariance sends the incidence fiber of `Y` to the incidence fiber
of `g Y`.
-/
theorem incidenceFiber_erlangen_image
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    (polar : Carrier → Carrier → R)
    (g : Carrier ≃ Carrier)
    (χ : R)
    (hχ : χ ≠ 0)
    (hcov :
      ∀ X Y : Carrier,
        polar (g X) (g Y) = χ * polar X Y)
    (Y : Carrier) :
    {Z : Carrier | polar Z (g Y) = 0}
      =
    g '' {X : Carrier | polar X Y = 0} := by
  ext Z
  constructor
  · intro hZ
    refine ⟨g.symm Z, ?_, ?_⟩
    · have hcov' := hcov (g.symm Z) Y
      simp at hcov'
      have hscaled : χ * polar (g.symm Z) Y = 0 := by
        rw [← hcov']
        exact hZ
      exact (mul_eq_zero.mp hscaled).resolve_left hχ
    · simp
  · rintro ⟨X, hX, rfl⟩
    change polar (g X) (g Y) = 0
    rw [hcov X Y, hX, mul_zero]

/--
Combined projective scaling plus Erlangen covariance for incidence fibers.
-/
theorem incidenceFiber_projective_erlangen_image
    {R Carrier : Type*}
    [CommRing R] [NoZeroDivisors R]
    [AddCommGroup Carrier] [Module R Carrier]
    (polar : Carrier → Carrier → R)
    (h_right :
      ∀ (μ : R) (X Y : Carrier),
        polar X (μ • Y) = μ * polar X Y)
    (g : Carrier ≃ Carrier)
    (χ : R)
    (hχ : χ ≠ 0)
    (hcov :
      ∀ X Y : Carrier,
        polar (g X) (g Y) = χ * polar X Y)
    (μ : R) (hμ : μ ≠ 0)
    (Y : Carrier) :
    {Z : Carrier | polar Z (g (μ • Y)) = 0}
      =
    g '' {X : Carrier | polar X Y = 0} := by
  calc
    {Z : Carrier | polar Z (g (μ • Y)) = 0}
        =
      g '' {X : Carrier | polar X (μ • Y) = 0} := by
        exact incidenceFiber_erlangen_image
          polar g χ hχ hcov (μ • Y)
    _ =
      g '' {X : Carrier | polar X Y = 0} := by
        exact congrArg (fun S : Set Carrier => g '' S)
          (incidenceFiber_scale_right polar h_right μ hμ Y)

end InfoGeometry.Projective.SplitOctonions.ProjectivePolarFiber
