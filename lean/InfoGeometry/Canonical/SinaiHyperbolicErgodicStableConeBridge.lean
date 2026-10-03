import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Matrix
open scoped Matrix

namespace SinaiBilliards

/-! ### 1. Setup & Invertible Matrix Foundation -/

def sinaiJacobian (τ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1 + τ * κ), -τ;
     -κ,           -1]

def sinaiJacobianInv (τ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1,           τ;
      κ, -(1 + τ * κ)]

lemma expand_mulVec_stable (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
  mulVec A v i = A i 0 * v 0 + A i 1 * v 1 := by
  rw [mulVec, dotProduct, Fin.sum_univ_two]

theorem sinaiJacobianInv_mul_sinaiJacobian (τ κ : ℝ) :
    sinaiJacobianInv τ κ * sinaiJacobian τ κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [sinaiJacobianInv, sinaiJacobian, one_apply]
    simp
    try ring
  )

noncomputable def lambdaU (u : ℝ) : ℝ :=
  (-(2 + u) - Real.sqrt (u * (u + 4))) / 2

noncomputable def lambdaS (u : ℝ) : ℝ :=
  (-(2 + u) + Real.sqrt (u * (u + 4))) / 2

noncomputable def eigenvecU (τ κ : ℝ) : Fin 2 → ℝ :=
  ![1 + lambdaU (τ * κ), -κ]

noncomputable def eigenvecS (τ κ : ℝ) : Fin 2 → ℝ :=
  ![1 + lambdaS (τ * κ), -κ]

/-! ### 2. Inverse Eigenvector Action -/

theorem toLin_apply_inv_eigenvecU {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Matrix.toLin' (sinaiJacobianInv τ κ) (eigenvecU τ κ) = lambdaS (τ * κ) • eigenvecU τ κ := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hsq : (Real.sqrt ((τ * κ) * (τ * κ + 4)))^2 - (τ * κ) * (τ * κ + 4) = 0 := by
    rw [Real.sq_sqrt hu_nonneg, sub_self]
  rw [toLin'_apply]
  ext i
  fin_cases i
  · rw [expand_mulVec_stable]
    dsimp [sinaiJacobianInv, eigenvecU, lambdaU, lambdaS]
    nlinarith [hsq]
  · rw [expand_mulVec_stable]
    dsimp [sinaiJacobianInv, eigenvecU, lambdaU, lambdaS]
    nlinarith [hsq]

theorem toLin_apply_inv_eigenvecS {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Matrix.toLin' (sinaiJacobianInv τ κ) (eigenvecS τ κ) = lambdaU (τ * κ) • eigenvecS τ κ := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hsq : (Real.sqrt ((τ * κ) * (τ * κ + 4)))^2 - (τ * κ) * (τ * κ + 4) = 0 := by
    rw [Real.sq_sqrt hu_nonneg, sub_self]
  rw [toLin'_apply]
  ext i
  fin_cases i
  · rw [expand_mulVec_stable]
    dsimp [sinaiJacobianInv, eigenvecS, lambdaU, lambdaS]
    nlinarith [hsq]
  · rw [expand_mulVec_stable]
    dsimp [sinaiJacobianInv, eigenvecS, lambdaU, lambdaS]
    nlinarith [hsq]

/-! ### 3. Backward Stable Cone Definitions -/

def stableCone (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  { v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧ |cu| ≤ α * |cs| }

def stableConeInt (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  { v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧ |cu| < α * |cs| ∧ cs ≠ 0 }

/-! ### 4. Spectral Contraction Ratio -/

lemma abs_lambdaS_lt_abs_lambdaU {u : ℝ} (hu : 0 < u) :
    |lambdaS u| < |lambdaU u| := by
  have hu4 : 0 < u * (u + 4) := mul_pos hu (by linarith)
  have hsqrt_pos : 0 < Real.sqrt (u * (u + 4)) := Real.sqrt_pos.mpr hu4
  have h_lt_sq : u * (u + 4) < (2 + u)^2 := by nlinarith
  have hsqrt_lt : Real.sqrt (u * (u + 4)) < 2 + u := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ 2 + u)]
    exact Real.sqrt_lt_sqrt (by positivity) h_lt_sq
  have h_s_neg : lambdaS u < 0 := by
    dsimp [lambdaS]; linarith
  have h_u_neg : lambdaU u < 0 := by
    dsimp [lambdaU]; linarith
  have h_abs_s : |lambdaS u| = (2 + u - Real.sqrt (u * (u + 4))) / 2 := by
    rw [abs_of_neg h_s_neg]; dsimp [lambdaS]; ring
  have h_abs_u : |lambdaU u| = (2 + u + Real.sqrt (u * (u + 4))) / 2 := by
    rw [abs_of_neg h_u_neg]; dsimp [lambdaU]; ring
  rw [h_abs_s, h_abs_u]
  linarith

/-! ### 5. Strict Backward Invariance Theorem -/

theorem strict_stable_cone_invariance {τ κ α : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α)
    {v : Fin 2 → ℝ} (hv : v ∈ stableCone τ κ α) (hv_ne : v ≠ 0) :
    Matrix.toLin' (sinaiJacobianInv τ κ) v ∈ stableConeInt τ κ α := by
  rcases hv with ⟨cu, cs, rfl, h_cone⟩
  have hu : 0 < τ * κ := mul_pos hτ hκ

  have hcs_ne : cs ≠ 0 := by
    intro hcs
    have hcu_zero : cu = 0 := by
      have hle : |cu| ≤ α * |cs| := h_cone
      rw [hcs, abs_zero, mul_zero] at hle
      exact abs_nonpos_iff.mp hle
    subst hcs
    subst hcu_zero
    simp only [zero_smul, add_zero] at hv_ne
    exact False.elim (hv_ne rfl)

  let L := Matrix.toLin' (sinaiJacobianInv τ κ)
  have h_lin : L (cu • eigenvecU τ κ + cs • eigenvecS τ κ) =
      (lambdaS (τ * κ) * cu) • eigenvecU τ κ + (lambdaU (τ * κ) * cs) • eigenvecS τ κ := by
    simp only [map_add, map_smul]
    rw [toLin_apply_inv_eigenvecU hτ hκ, toLin_apply_inv_eigenvecS hτ hκ]
    rw [smul_smul, smul_smul, mul_comm cu, mul_comm cs]

  use lambdaS (τ * κ) * cu, lambdaU (τ * κ) * cs
  refine ⟨h_lin, ?_, ?_⟩
  · rw [abs_mul, abs_mul]
    have h_ratio := abs_lambdaS_lt_abs_lambdaU hu
    have h_cs_pos : 0 < |cs| := abs_pos.mpr hcs_ne
    have h_bound : |lambdaS (τ * κ)| * |cu| ≤ |lambdaS (τ * κ)| * (α * |cs|) :=
      mul_le_mul_of_nonneg_left h_cone (abs_nonneg _)
    have h_strict : |lambdaS (τ * κ)| * (α * |cs|) < |lambdaU (τ * κ)| * (α * |cs|) := by
      have h_coeff : 0 < α * |cs| := mul_pos hα h_cs_pos
      exact mul_lt_mul_of_pos_right h_ratio h_coeff
    calc
      |lambdaS (τ * κ)| * |cu| ≤ |lambdaS (τ * κ)| * (α * |cs|) := h_bound
      _ < |lambdaU (τ * κ)| * (α * |cs|) := h_strict
      _ = α * (|lambdaU (τ * κ)| * |cs|) := by ring
  · have h_u_ne : lambdaU (τ * κ) ≠ 0 := by
      have hu4 : 0 < (τ * κ) * (τ * κ + 4) := mul_pos hu (by linarith)
      dsimp [lambdaU]
      intro h
      have : -(2 + τ * κ) - Real.sqrt ((τ * κ) * (τ * κ + 4)) = 0 := by linarith
      have : 0 < Real.sqrt ((τ * κ) * (τ * κ + 4)) := Real.sqrt_pos.mpr hu4
      linarith
    exact mul_ne_zero h_u_ne hcs_ne

theorem stable_cone_image_subset_int {τ κ α : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α) :
    (Matrix.toLin' (sinaiJacobianInv τ κ)) '' (stableCone τ κ α \ {0}) ⊆ stableConeInt τ κ α := by
  rintro w ⟨v, ⟨hv_cone, hv_ne⟩, rfl⟩
  exact strict_stable_cone_invariance hτ hκ hα hv_cone hv_ne

end SinaiBilliards
