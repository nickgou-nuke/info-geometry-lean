import InfoGeometry.Canonical.PrimitiveCuntzIsometry

open InfoGeometry.GrandUnification.UHF
open PrimitiveCuntzIsometry

noncomputable section

namespace PrimitiveCuntzCohomology

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]
variable [UHF : UHFAlgebra A]

/-- 
The exact boundary differential $\partial$ constructed from the Cuntz isometries.
By combining the left generator and right annihilator, we create a chiral 
nilpotent operator that maps the right vacuum into the left vacuum.
-/
def UHF_boundary : A := UHFAlgebra.S_L * star UHFAlgebra.S_R

/--
Theorem: Dual Cuntz Orthogonality.
Since `S_L^* S_R = 0`, its adjoint `S_R^* S_L = 0` as well.
-/
theorem cuntz_dual_orthogonality : star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_L (A := A) = 0 := by
  have h := cuntz_orthogonality (A := A)
  have h_star : star (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_R (A := A)) = star (0 : A) := by rw [h]
  rw [star_zero, star_mul, star_star] at h_star
  exact h_star

/--
Theorem: Cohomological Nilpotence ($\partial^2 = 0$).
The boundary differential is strictly nilpotent due to the primitive exactness
of the Cuntz partition. The image of $\partial$ perfectly annihilates under
a second application, guaranteeing no topological leakage in the UHF limit.
-/
theorem UHF_boundary_sq_eq_zero : UHF_boundary (A := A) * UHF_boundary (A := A) = 0 := by
  dsimp [UHF_boundary]
  calc
    (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) * (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A)))
      = UHFAlgebra.S_L (A := A) * (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_L (A := A)) * star (UHFAlgebra.S_R (A := A)) := by simp only [mul_assoc]
    _ = UHFAlgebra.S_L (A := A) * 0 * star (UHFAlgebra.S_R (A := A)) := by rw [cuntz_dual_orthogonality]
    _ = 0 := by simp

/--
The Hodge-Dirac Laplacian for the UHF algebra.
$\Delta = \partial \partial^* + \partial^* \partial$
-/
def UHF_Laplacian : A := 
  UHF_boundary * star UHF_boundary + star UHF_boundary * UHF_boundary

/--
Theorem: The exact sequence resolves to the Identity Laplacian.
By summing the chiral boundaries, the Laplacian perfectly recovers the exact 
primitive projection sequence, stabilizing the vacuum state.
This records the algebraic Laplacian identity for the abstract Cuntz/UHF
carrier.  It does not by itself assert a full computed cohomology group.
-/
theorem UHF_Laplacian_eq_one : UHF_Laplacian (A := A) = 1 := by
  dsimp [UHF_Laplacian, UHF_boundary]
  have step1 : (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) * star (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A)))
      = UHFAlgebra.S_L (A := A) * (star (UHFAlgebra.S_R (A := A)) * UHFAlgebra.S_R (A := A)) * star (UHFAlgebra.S_L (A := A)) := by
    rw [star_mul, star_star]
    simp only [mul_assoc]
  rw [UHFAlgebra.isometry_R] at step1
  have step1_final : (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) * star (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) = P_L (A := A) := by
    calc
      _ = UHFAlgebra.S_L (A := A) * 1 * star (UHFAlgebra.S_L (A := A)) := step1
      _ = P_L (A := A) := by simp [P_L]
  
  have step2 : star (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) * (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A)))
      = UHFAlgebra.S_R (A := A) * (star (UHFAlgebra.S_L (A := A)) * UHFAlgebra.S_L (A := A)) * star (UHFAlgebra.S_R (A := A)) := by
    rw [star_mul, star_star]
    simp only [mul_assoc]
  rw [UHFAlgebra.isometry_L] at step2
  have step2_final : star (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) * (UHFAlgebra.S_L (A := A) * star (UHFAlgebra.S_R (A := A))) = P_R (A := A) := by
    calc
      _ = UHFAlgebra.S_R (A := A) * 1 * star (UHFAlgebra.S_R (A := A)) := step2
      _ = P_R (A := A) := by simp [P_R]
  
  rw [step1_final, step2_final]
  exact cuntz_partition_exactness

end PrimitiveCuntzCohomology
