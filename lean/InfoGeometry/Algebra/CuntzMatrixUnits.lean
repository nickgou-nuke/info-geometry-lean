import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Cuntz Matrix Units: E_{ij} = S_i Sdag_j

Proved: E_{ij} E_{kl} = δ_{jk} E_{il} (matrix unit multiplication).
Uses explicit `mul_assoc` + `cuntz_orthogonality`. No `simp` magic.
-/
open InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzMatrixUnits

def E (n : ℕ) (i j : Fin n) : CuntzAlg n := cuntzS n i * cuntzSdag n j

/-- Matrix unit multiplication: E_{ij} E_{kl} = δ_{jk} E_{il} -/
theorem matrix_unit_mul (n : ℕ) (i j k l : Fin n) :
    E n i j * E n k l = (if j = k then E n i l else 0) := by
  dsimp [E]
  -- (S_i Sdag_j)(S_k Sdag_l) = S_i (Sdag_j S_k) Sdag_l = S_i (δ_{jk}) Sdag_l
  calc
    (cuntzS n i * cuntzSdag n j) * (cuntzS n k * cuntzSdag n l)
        = cuntzS n i * (cuntzSdag n j * cuntzS n k) * cuntzSdag n l := by
      simp [mul_assoc]
    _ = cuntzS n i * (if j = k then 1 else 0) * cuntzSdag n l := by
      rw [cuntz_orthogonality n j k]
    _ = (if j = k then cuntzS n i * 1 * cuntzSdag n l
         else cuntzS n i * 0 * cuntzSdag n l) := by split_ifs <;> rfl
    _ = (if j = k then cuntzS n i * cuntzSdag n l else 0) := by
      split_ifs <;> simp

/-- Matrix unit dagger: E_{ij}† = E_{ji} -/
theorem matrix_unit_star (n : ℕ) (i j : Fin n) :
    star (E n i j) = E n j i := by
  simp [E, star_mul, star_cuntzS, star_cuntzSdag]

/-- Diagonal matrix units are the range projectors: E_{ii} = P_i -/
theorem matrix_unit_diag_eq_projector (n : ℕ) (i : Fin n) :
    E n i i = cuntzS n i * cuntzSdag n i := rfl

/-- Matrix units are partial isometries: E_{ij} E_{ji} = P_i -/
theorem matrix_unit_partial_isometry (n : ℕ) (i j : Fin n) :
    E n i j * E n j i = cuntzS n i * cuntzSdag n i := by
  calc
    E n i j * E n j i = (if j = j then E n i i else 0) := matrix_unit_mul n i j j i
    _ = E n i i := by simp
    _ = cuntzS n i * cuntzSdag n i := rfl

/-- Square of off-diagonal matrix unit vanishes: E_{ij}^2 = 0 for i≠j -/
theorem matrix_unit_sq_off_diag (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    E n i j * E n i j = 0 := by
  rw [matrix_unit_mul n i j i j]
  simp [hij, Ne.symm hij]

/-- Matrix units form a complete system: Σ_i E_{ii} = Σ_i P_i = 1 -/
theorem matrix_unit_sum_diag_eq_one (n : ℕ) :
    (∑ i : Fin n, E n i i) = 1 := by
  simp [E, cuntz_ranges_sum_one n]

end InfoGeometry.Algebra.CuntzMatrixUnits
