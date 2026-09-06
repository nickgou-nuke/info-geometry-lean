import InfoGeometry.Projective.KleinQuadric
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.KleinQuadricIncidence

Concrete incidence kernel on the Klein-quadric line space.

This file adds:

* a symmetric bilinear line-incidence pairing on Plücker coordinates;
* incidence fibers as zero loci of that pairing;
* Erlangen-style fiber transport under an equivalence preserving the pairing
  up to a nonzero scalar.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Projective.KleinQuadricIncidence

open KleinQuadric

namespace Plucker6

variable {R : Type*} [CommRing R]

/--
Klein line-incidence pairing.

For Plücker coordinates `(p01,p02,p03,p12,p13,p23)` and
`(q01,q02,q03,q12,q13,q23)`, the standard bilinear form is

`p01*q23 - p02*q13 + p03*q12 + p12*q03 - p13*q02 + p23*q01`.
-/
def incidenceForm (P Q : Plucker6 R) : R :=
  P.p01 * Q.p23 - P.p02 * Q.p13 + P.p03 * Q.p12
    + P.p12 * Q.p03 - P.p13 * Q.p02 + P.p23 * Q.p01

/--
The incidence pairing is exactly the polar form attached to the Klein quadric
from `InfoGeometry.Projective.KleinQuadric`.
-/
@[simp] theorem incidenceForm_eq_polar (P Q : Plucker6 R) :
    incidenceForm P Q = Plucker6.polar P Q := by
  rw [Plucker6.polar_formula]
  unfold incidenceForm
  ring

@[simp] theorem incidenceForm_symm (P Q : Plucker6 R) :
    incidenceForm P Q = incidenceForm Q P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold incidenceForm
  ring

/-- Left homogeneity of incidence form. -/
@[simp] theorem incidenceForm_scale_left (l : R) (P Q : Plucker6 R) :
    incidenceForm (Plucker6.scale l P) Q = l * incidenceForm P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold incidenceForm Plucker6.scale
  ring

/-- Right homogeneity of incidence form. -/
@[simp] theorem incidenceForm_scale_right (m : R) (P Q : Plucker6 R) :
    incidenceForm P (Plucker6.scale m Q) = m * incidenceForm P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold incidenceForm Plucker6.scale
  ring

/-- Incidence fiber through a fixed line-coordinate point `Y`. -/
def incidenceFiber (Y : Plucker6 R) : Set (Plucker6 R) :=
  {X | incidenceForm X Y = 0}

/-- Left representative rescaling does not change the incidence fiber. -/
  theorem incidenceFiber_scale_left
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0)
    (Y : Plucker6 R) :
    {X : Plucker6 R | incidenceForm (Plucker6.scale l X) Y = 0}
      =
    {X : Plucker6 R | incidenceForm X Y = 0} := by
  ext X
  change (incidenceForm (Plucker6.scale l X) Y = 0 ↔ incidenceForm X Y = 0)
  rw [incidenceForm_scale_left]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hl
  · intro h
    rw [h, mul_zero]

/-- Right representative rescaling does not change the incidence fiber. -/
  theorem incidenceFiber_scale_right
    [NoZeroDivisors R]
    (m : R) (hm : m ≠ 0)
    (Y : Plucker6 R) :
    {X : Plucker6 R | incidenceForm X (Plucker6.scale m Y) = 0}
      =
    {X : Plucker6 R | incidenceForm X Y = 0} := by
  ext X
  change (incidenceForm X (Plucker6.scale m Y) = 0 ↔ incidenceForm X Y = 0)
  rw [incidenceForm_scale_right]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hm
  · intro h
    rw [h, mul_zero]

/--
Erlangen covariance sends the incidence fiber of `Y` to the incidence fiber of
`g Y`.
-/
theorem incidenceFiber_erlangen_image
    [NoZeroDivisors R]
    (g : Plucker6 R ≃ Plucker6 R)
    (chi : R)
    (hchi : chi ≠ 0)
    (hcov : ∀ X Y : Plucker6 R, incidenceForm (g X) (g Y) = chi * incidenceForm X Y)
    (Y : Plucker6 R) :
    {Z : Plucker6 R | incidenceForm Z (g Y) = 0}
      =
    g '' {X : Plucker6 R | incidenceForm X Y = 0} := by
  ext Z
  constructor
  · intro hZ
    refine ⟨g.symm Z, ?_, ?_⟩
    · have hcov' : incidenceForm Z (g Y) = chi * incidenceForm (g.symm Z) Y := by
        simpa using hcov (g.symm Z) Y
      have hscaled : chi * incidenceForm (g.symm Z) Y = 0 := by
        rw [← hcov']
        exact hZ
      exact (mul_eq_zero.mp hscaled).resolve_left hchi
    · simp
  · rintro ⟨X, hX, rfl⟩
    change incidenceForm (g X) (g Y) = 0
    rw [hcov X Y, hX, mul_zero]

/--
Combined projective scaling plus Erlangen covariance for Klein incidence
fibers.
-/
theorem incidenceFiber_projective_erlangen_image
    [NoZeroDivisors R]
    (g : Plucker6 R ≃ Plucker6 R)
    (chi : R)
    (hchi : chi ≠ 0)
    (hcov : ∀ X Y : Plucker6 R, incidenceForm (g X) (g Y) = chi * incidenceForm X Y)
    (m : R) (hm : m ≠ 0)
    (Y : Plucker6 R) :
    {Z : Plucker6 R | incidenceForm Z (g (Plucker6.scale m Y)) = 0}
      =
    g '' {X : Plucker6 R | incidenceForm X Y = 0} := by
  calc
    {Z : Plucker6 R | incidenceForm Z (g (Plucker6.scale m Y)) = 0}
        =
      g '' {X : Plucker6 R | incidenceForm X (Plucker6.scale m Y) = 0} := by
        exact incidenceFiber_erlangen_image g chi hchi hcov (Plucker6.scale m Y)
    _ =
      g '' {X : Plucker6 R | incidenceForm X Y = 0} := by
        exact congrArg (fun S : Set (Plucker6 R) => g '' S)
          (incidenceFiber_scale_right m hm Y)

end Plucker6

end InfoGeometry.Projective.KleinQuadricIncidence
