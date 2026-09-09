import Mathlib
namespace InfoGeometry.SignedNetwork.CoherenceAndProjection
noncomputable section
open scoped Matrix
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
def conjugate (U P : Mat2) := U * P * Uᴴ
theorem conjugate_idempotent (U P : Mat2) (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hP : P*P=P) :
    conjugate U P * conjugate U P = conjugate U P := by
  unfold conjugate
  calc
    (U * P * Uᴴ) * (U * P * Uᴴ) = U * P * (Uᴴ * U) * P * Uᴴ := by
      simp only [Matrix.mul_assoc]
    _ = U * (P * P) * Uᴴ := by rw [hU]; simp only [mul_one, Matrix.mul_assoc]
    _ = U * P * Uᴴ := by rw [hP]
theorem conjugate_identity (U : Mat2) (hU' : U * Uᴴ = 1) : conjugate U 1 = 1 := by
  simp [conjugate, hU']
end
end InfoGeometry.SignedNetwork.CoherenceAndProjection
