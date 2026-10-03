import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.SinaiHyperbolicErgodicMixingBridge

open Matrix

local notation "RealMat" => Matrix (Fin 2) (Fin 2) ℝ

def flightShear (τ : ℝ) : RealMat := !![1, τ; 0, 1]
def reflectionShear (κ : ℝ) : RealMat := !![1, 0; κ, 1]
def sinaiJacobian (τ κ : ℝ) : RealMat := -(flightShear τ * reflectionShear κ)

lemma mat_mul_expand (A B : RealMat) (i j : Fin 2) :
  (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem sinaiJacobian_eq (τ κ : ℝ) : 
  sinaiJacobian τ κ = !![-(1 + τ * κ), -τ; -κ, -1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change -(flightShear τ * reflectionShear κ) 0 0 = -(1 + τ * κ)
    rw [mat_mul_expand]
    dsimp [flightShear, reflectionShear]; ring
  · change -(flightShear τ * reflectionShear κ) 0 1 = -τ
    rw [mat_mul_expand]
    dsimp [flightShear, reflectionShear]; ring
  · change -(flightShear τ * reflectionShear κ) 1 0 = -κ
    rw [mat_mul_expand]
    dsimp [flightShear, reflectionShear]; ring
  · change -(flightShear τ * reflectionShear κ) 1 1 = -1
    rw [mat_mul_expand]
    dsimp [flightShear, reflectionShear]; ring

theorem sinaiJacobian_det (τ κ : ℝ) : 
  (sinaiJacobian τ κ).det = 1 := by
  rw [sinaiJacobian_eq, det_fin_two]
  change (-(1 + τ * κ)) * (-1) - (-τ) * (-κ) = 1
  ring

lemma matrix_trace_fin_two (A : RealMat) : 
  Matrix.trace A = A 0 0 + A 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]

theorem sinaiJacobian_trace (τ κ : ℝ) : 
  Matrix.trace (sinaiJacobian τ κ) = -(2 + τ * κ) := by
  rw [sinaiJacobian_eq, matrix_trace_fin_two]
  change (-(1 + τ * κ)) + (-1) = -(2 + τ * κ)
  ring

theorem sinai_strict_hyperbolicity (τ κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ) : 
  Matrix.trace (sinaiJacobian τ κ) < -2 := by
  rw [sinaiJacobian_trace]
  have h_pos : 0 < τ * κ := mul_pos hτ hκ
  linarith

def sinaiDiscriminant (τ κ : ℝ) : ℝ :=
  (Matrix.trace (sinaiJacobian τ κ))^2 - 4

theorem sinaiDiscriminant_eq (τ κ : ℝ) : 
  sinaiDiscriminant τ κ = (τ * κ) * (τ * κ + 4) := by
  dsimp [sinaiDiscriminant]
  rw [sinaiJacobian_trace]
  ring

theorem sinaiDiscriminant_pos (τ κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ) : 
  0 < sinaiDiscriminant τ κ := by
  rw [sinaiDiscriminant_eq]
  have h_pos : 0 < τ * κ := mul_pos hτ hκ
  have h_add : 0 < τ * κ + 4 := by linarith
  exact mul_pos h_pos h_add

def sinaiCharPoly (τ κ L : ℝ) : ℝ :=
  L^2 - (Matrix.trace (sinaiJacobian τ κ)) * L + (sinaiJacobian τ κ).det

noncomputable def sinaiEigenvalueUnstable (τ κ : ℝ) : ℝ :=
  (-(2 + τ * κ) - Real.sqrt (sinaiDiscriminant τ κ)) / 2

noncomputable def sinaiEigenvalueStable (τ κ : ℝ) : ℝ :=
  (-(2 + τ * κ) + Real.sqrt (sinaiDiscriminant τ κ)) / 2

theorem sinaiEigenvalue_product (τ κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ) : 
  sinaiEigenvalueUnstable τ κ * sinaiEigenvalueStable τ κ = 1 := by
  dsimp [sinaiEigenvalueUnstable, sinaiEigenvalueStable]
  have h_disc_pos : 0 ≤ sinaiDiscriminant τ κ := le_of_lt (sinaiDiscriminant_pos τ κ hτ hκ)
  have h_sqrt : (Real.sqrt (sinaiDiscriminant τ κ))^2 = sinaiDiscriminant τ κ := Real.sq_sqrt h_disc_pos
  calc (-(2 + τ * κ) - Real.sqrt (sinaiDiscriminant τ κ)) / 2 * ((-(2 + τ * κ) + Real.sqrt (sinaiDiscriminant τ κ)) / 2)
    _ = ((-(2 + τ * κ))^2 - (Real.sqrt (sinaiDiscriminant τ κ))^2) / 4 := by ring
    _ = ((-(2 + τ * κ))^2 - sinaiDiscriminant τ κ) / 4 := by rw [h_sqrt]
    _ = 1 := by rw [sinaiDiscriminant_eq]; ring

theorem sinaiEigenvalueUnstable_lt_neg_one (τ κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ) : 
  sinaiEigenvalueUnstable τ κ < -1 := by
  dsimp [sinaiEigenvalueUnstable]
  have h_tk : 0 < τ * κ := mul_pos hτ hκ
  have h_disc : 0 < Real.sqrt (sinaiDiscriminant τ κ) := 
    Real.sqrt_pos.mpr (sinaiDiscriminant_pos τ κ hτ hκ)
  linarith

end InfoGeometry.Canonical.SinaiHyperbolicErgodicMixingBridge
