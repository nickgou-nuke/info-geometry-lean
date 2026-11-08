import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
import InfoGeometry.Quantum.DoubledCPTModularBridge

open Matrix
open scoped Matrix
open scoped Kronecker
open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
open InfoGeometry.Quantum.DoubledCPTModularBridge

namespace InfoGeometry.Quantum.DoubledJacobianBipartiteInvariance

def sinaiJacobianInv (τ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1,           τ;
      κ, -(1 + τ * κ)]

/-- The 4x4 doubled evolution matrix J ⊗ J⁻¹ on the bipartite system. -/
def sinaiDoubledJacobian (τ κ : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  sinaiJacobian τ κ ⊗ₖ sinaiJacobianInv τ κ

/-- The canonical tensor product of two 2D vectors: (v ⊗ w)_(i, j) = v_i * w_j. -/
def tensorVec (v w : Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun ⟨i, j⟩ => v i * w j

/-- The maximally entangled diagonal state |Ω⟩ = v_u ⊗ v_u + v_s ⊗ v_s. -/
noncomputable def diagonalEntangledState (τ κ : ℝ) : Fin 2 × Fin 2 → ℝ :=
  tensorVec (eigenvecU τ κ) (eigenvecU τ κ) + tensorVec (eigenvecS τ κ) (eigenvecS τ κ)

/-- General Thermofield Double state with arbitrary weights c_u, c_s. -/
noncomputable def tfdState (τ κ cu cs : ℝ) : Fin 2 × Fin 2 → ℝ :=
  cu • tensorVec (eigenvecU τ κ) (eigenvecU τ κ) + cs • tensorVec (eigenvecS τ κ) (eigenvecS τ κ)

theorem sinaiJacobianInv_mulVec_eigenvecU {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiJacobianInv τ κ) (eigenvecU τ κ) = lambdaS (τ * κ) • eigenvecU τ κ := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hsq : (Real.sqrt ((τ * κ) * (τ * κ + 4)))^2 = (τ * κ) * (τ * κ + 4) :=
    Real.sq_sqrt hu_nonneg
  ext i
  fin_cases i
  · simp [sinaiJacobianInv, eigenvecU, mulVec, dotProduct, lambdaU, lambdaS, Fin.sum_univ_two, smul_eq_mul]
    linear_combination 1/4 * hsq
  · simp [sinaiJacobianInv, eigenvecU, mulVec, dotProduct, lambdaU, lambdaS, Fin.sum_univ_two, smul_eq_mul]
    ring

theorem sinaiJacobianInv_mulVec_eigenvecS {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiJacobianInv τ κ) (eigenvecS τ κ) = lambdaU (τ * κ) • eigenvecS τ κ := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hsq : (Real.sqrt ((τ * κ) * (τ * κ + 4)))^2 = (τ * κ) * (τ * κ + 4) :=
    Real.sq_sqrt hu_nonneg
  ext i
  fin_cases i
  · simp [sinaiJacobianInv, eigenvecS, mulVec, dotProduct, lambdaU, lambdaS, Fin.sum_univ_two, smul_eq_mul]
    linear_combination 1/4 * hsq
  · simp [sinaiJacobianInv, eigenvecS, mulVec, dotProduct, lambdaU, lambdaS, Fin.sum_univ_two, smul_eq_mul]
    ring

lemma mulVec_kronecker_tensorVec (A B : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 → ℝ) :
    mulVec (A ⊗ₖ B) (tensorVec v w) = tensorVec (mulVec A v) (mulVec B w) := by
  ext ⟨i, j⟩
  dsimp [mulVec, dotProduct, tensorVec, Matrix.kroneckerMap]
  have h1 : (∑ x : Fin 2 × Fin 2, A i x.1 * B j x.2 * (v x.1 * w x.2)) =
      ∑ k : Fin 2, ∑ l : Fin 2, A i k * B j l * (v k * w l) := by
    exact Finset.sum_product' Finset.univ Finset.univ (fun k l => (A i k * B j l * (v k * w l) : ℝ))
  rw [h1]
  simp [Fin.sum_univ_two]
  ring

lemma tensorVec_smul_smul (a b : ℝ) (v w : Fin 2 → ℝ) :
    tensorVec (a • v) (b • w) = (a * b) • tensorVec v w := by
  ext ⟨i, j⟩
  dsimp [tensorVec]
  change (a * v i) * (b * w j) = (a * b) * (v i * w j); ring

/-- Under J ⊗ J⁻¹, the pure state v_u ⊗ v_u is fixed with eigenvalue λ_u * λ_s = 1. -/
theorem doubledJacobian_mulVec_uu {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiDoubledJacobian τ κ) (tensorVec (eigenvecU τ κ) (eigenvecU τ κ)) =
      tensorVec (eigenvecU τ κ) (eigenvecU τ κ) := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  dsimp [sinaiDoubledJacobian]
  rw [mulVec_kronecker_tensorVec]
  rw [sinaiJacobian_mulVec_eigenvecU hτ hκ]
  rw [sinaiJacobianInv_mulVec_eigenvecU hτ hκ]
  rw [tensorVec_smul_smul]
  rw [lambdaU_mul_lambdaS (τ * κ) hu_nonneg]
  rw [one_smul]

/-- Under J ⊗ J⁻¹, the pure state v_s ⊗ v_s is fixed with eigenvalue λ_s * λ_u = 1. -/
theorem doubledJacobian_mulVec_ss {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiDoubledJacobian τ κ) (tensorVec (eigenvecS τ κ) (eigenvecS τ κ)) =
      tensorVec (eigenvecS τ κ) (eigenvecS τ κ) := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  dsimp [sinaiDoubledJacobian]
  rw [mulVec_kronecker_tensorVec]
  rw [sinaiJacobian_mulVec_eigenvecS hτ hκ]
  rw [sinaiJacobianInv_mulVec_eigenvecS hτ hκ]
  rw [tensorVec_smul_smul]
  rw [mul_comm (lambdaS (τ * κ)), lambdaU_mul_lambdaS (τ * κ) hu_nonneg]
  rw [one_smul]

/-- Core Theorem: The doubled collision map J ⊗ J⁻¹ strictly fixes
    the maximally entangled diagonal state |Ω⟩ across the bipartite system. -/
theorem doubledJacobian_fixes_diagonalState {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiDoubledJacobian τ κ) (diagonalEntangledState τ κ) =
      diagonalEntangledState τ κ := by
  dsimp [diagonalEntangledState]
  rw [Matrix.mulVec_add]
  rw [doubledJacobian_mulVec_uu hτ hκ]
  rw [doubledJacobian_mulVec_ss hτ hκ]

/-- Thermofield Double Invariance: J ⊗ J⁻¹ fixes any weighted TFD state. -/
theorem doubledJacobian_fixes_tfdState {τ κ cu cs : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiDoubledJacobian τ κ) (tfdState τ κ cu cs) =
      tfdState τ κ cu cs := by
  dsimp [tfdState]
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [doubledJacobian_mulVec_uu hτ hκ]
  rw [doubledJacobian_mulVec_ss hτ hκ]

end InfoGeometry.Quantum.DoubledJacobianBipartiteInvariance
