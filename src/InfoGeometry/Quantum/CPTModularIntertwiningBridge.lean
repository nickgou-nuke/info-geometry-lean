import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic
import InfoGeometry.Quantum.DoubledJacobianBipartiteInvariance

open Matrix
open scoped Matrix
open scoped Kronecker
open InfoGeometry.Quantum.DoubledJacobianBipartiteInvariance
open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

namespace InfoGeometry.Quantum.CPTModularIntertwiningBridge

/-- The modular swap operator Θ on the doubled space ℝ² ⊗ ℝ², mapping v ⊗ w to w ⊗ v. -/
def cptSwap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  fun ⟨i, j⟩ ⟨k, l⟩ => if i = l ∧ j = k then 1 else 0

/-- Θ is an involution: Θ² = I. -/
lemma cptSwap_mul_cptSwap : cptSwap * cptSwap = (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [Matrix.mul_apply, Matrix.one_apply]
  dsimp [cptSwap, dotProduct]
  rw [Fintype.sum_prod_type]
  have h1 : (∑ x : Fin 2, ∑ y : Fin 2, (if i = y ∧ j = x then (1:ℝ) else 0) * (if x = l ∧ y = k then 1 else 0)) =
      if i = k ∧ j = l then (1:ℝ) else 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp
  rw [h1]
  congr 1
  ext
  simp

/-- Θ swaps the Kronecker tensor factors: Θ (A ⊗ B) = (B ⊗ A) Θ. -/
lemma cptSwap_mul_kronecker (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    cptSwap * (A ⊗ₖ B) = (B ⊗ₖ A) * cptSwap := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [Matrix.mul_apply, Matrix.mul_apply]
  dsimp [cptSwap, kroneckerMap]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have h1 : (∑ x : Fin 2, ∑ y : Fin 2, (if i = y ∧ j = x then (1:ℝ) else 0) * (A x k * B y l)) = A j k * B i l := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp
  have h2 : (∑ x : Fin 2, ∑ y : Fin 2, (B i x * A j y) * (if x = l ∧ y = k then (1:ℝ) else 0)) = B i l * A j k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp
  rw [h1, h2]
  ring

lemma sinaiJacobianInv_is_inv (τ κ : ℝ) :
    sinaiJacobianInv τ κ * sinaiJacobian τ κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sinaiJacobianInv, sinaiJacobian, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Matrix.one_apply] <;> ring

lemma sinaiJacobianInv_is_inv_right (τ κ : ℝ) :
    sinaiJacobian τ κ * sinaiJacobianInv τ κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sinaiJacobianInv, sinaiJacobian, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Matrix.one_apply] <;> ring

/-- The CPT swap involution Θ strictly inverts the doubled collision flow. -/
theorem cpt_inverts_doubled_jacobian {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    cptSwap * sinaiDoubledJacobian τ κ * cptSwap = (sinaiDoubledJacobian τ κ)⁻¹ := by
  have h_cpt_eq : cptSwap * sinaiDoubledJacobian τ κ * cptSwap = sinaiJacobianInv τ κ ⊗ₖ sinaiJacobian τ κ := by
    dsimp [sinaiDoubledJacobian]
    rw [cptSwap_mul_kronecker]
    rw [Matrix.mul_assoc]
    rw [cptSwap_mul_cptSwap]
    rw [Matrix.mul_one]
  rw [h_cpt_eq]
  symm
  apply inv_eq_right_inv
  dsimp [sinaiDoubledJacobian]
  rw [← Matrix.mul_kronecker_mul]
  rw [sinaiJacobianInv_is_inv]
  rw [sinaiJacobianInv_is_inv_right]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [kroneckerMap, Matrix.one_apply]
  split_ifs <;> aesop

end InfoGeometry.Quantum.CPTModularIntertwiningBridge
