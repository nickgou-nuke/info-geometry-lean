import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzUHFAlgebra
import InfoGeometry.Canonical.PrimitiveCuntzIsometry

noncomputable section

namespace InfoGeometry.Dynamics.VOA

open Complex
open InfoGeometry.GrandUnification.UHF
open InfoGeometry.Canonical.PrimitiveCuntzIsometry

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
variable [UHF : UHFAlgebra A]

/-- The dual orthogonality S_R^* S_L = 0 derived from S_L^* S_R = 0 -/
theorem cuntz_orthogonality_symm : star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_L (A := A) = 0 := by
  have h1 : star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A) = 0 := cuntz_orthogonality
  have h2 : star (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A)) = star (0 : A) := by rw [h1]
  rw [star_mul, star_star, star_zero] at h2
  exact h2

/-- 
The Vertex Operator Algebra (VOA) state creation.
The vacuum state |0> corresponds to the identity operator in the Cuntz algebra.
The creation of a string excitation corresponds to applying the Cuntz isometry S_L
as an alpha_{-1} oscillator.
-/
def string_creation (X : A) : A :=
  UHFAlgebra.S_L (A := A) * X * star (UHFAlgebra.S_L (A := A))

/-- 
The Vertex Operator Algebra (VOA) state annihilation.
The destruction of a string excitation corresponds to applying the adjoint S_L^*
as an alpha_{+1} oscillator.
-/
def string_annihilation (X : A) : A :=
  star (UHFAlgebra.S_L (A := A)) * X * UHFAlgebra.S_L (A := A)

/--
Theorem: Heisenberg oscillator relation on the Cuntz tree.
The annihilation of a created string state exactly returns the original state,
certifying the [alpha_1, alpha_{-1}] = 1 commutation on the vacuum.
-/
theorem heisenberg_commutation (X : A) : 
    string_annihilation (string_creation X) = X := by
  dsimp [string_creation, string_annihilation]
  calc
    star (UHFAlgebra.S_L (A := A)) * (UHFAlgebra.S_L (A := A) * X * star (UHFAlgebra.S_L (A := A))) * UHFAlgebra.S_L (A := A)
      = (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_L (A := A)) * X * (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_L (A := A)) := by simp [mul_assoc]
    _ = 1 * X * 1 := by rw [UHFAlgebra.isometry_L]
    _ = X := by simp

/--
Theorem: Orthogonal state suppression (String Theory Selection Rule).
Attempting to annihilate an S_L excitation with an S_R operator strictly evaluates
to zero. This is the VOA expression of Primitive Exactness (Zero Holonomy).
-/
theorem orthogonal_string_suppression (X : A) :
    star (UHFAlgebra.S_R (A := A)) * string_creation X * UHFAlgebra.S_R (A := A) = 0 := by
  dsimp [string_creation]
  calc
    star (UHFAlgebra.S_R (A := A)) * (UHFAlgebra.S_L (A := A) * X * star (UHFAlgebra.S_L (A := A))) * UHFAlgebra.S_R (A := A)
      = (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_L (A := A)) * X * (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A)) := by simp [mul_assoc]
    _ = 0 * X * 0 := by rw [cuntz_orthogonality_symm, cuntz_orthogonality]
    _ = 0 := by simp

end InfoGeometry.Dynamics.VOA
