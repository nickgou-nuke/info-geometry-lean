import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

open Matrix
open scoped Matrix

namespace InfoGeometry.Canonical.SinaiHyperbolicErgodicStableConeBridge

open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

/-- Inverse of the repository-owned Sinai collision Jacobian. -/
def sinaiJacobianInv (τ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1,           τ;
      κ, -(1 + τ * κ)]

/-- The displayed matrix is a left inverse of the Sinai collision Jacobian. -/
theorem sinaiJacobianInv_mul_sinaiJacobian (τ κ : ℝ) :
    sinaiJacobianInv τ κ * sinaiJacobian τ κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sinaiJacobianInv, sinaiJacobian, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- The displayed matrix is also a right inverse. -/
theorem sinaiJacobian_mul_sinaiJacobianInv (τ κ : ℝ) :
    sinaiJacobian τ κ * sinaiJacobianInv τ κ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sinaiJacobianInv, sinaiJacobian, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-! The inverse swaps the stable and unstable eigenvalues, using the existing
eigenvalue and eigenvector definitions from the cone-field owner. -/

theorem toLin_apply_inv_eigenvecU {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Matrix.toLin' (sinaiJacobianInv τ κ) (eigenvecU τ κ) =
      lambdaS (τ * κ) • eigenvecU τ κ := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have hu : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hsq : (Real.sqrt ((τ * κ) * (τ * κ + 4))) ^ 2 =
      (τ * κ) * (τ * κ + 4) := Real.sq_sqrt hu_nonneg
  rw [toLin'_apply]
  ext i
  fin_cases i
  · rw [SinaiHyperbolicErgodicConeFieldBridge.expand_mulVec]
    dsimp [sinaiJacobianInv, eigenvecU, lambdaU, lambdaS]
    nlinarith [hsq]
  · rw [SinaiHyperbolicErgodicConeFieldBridge.expand_mulVec]
    dsimp [sinaiJacobianInv, eigenvecU, lambdaU, lambdaS]
    ring

theorem toLin_apply_inv_eigenvecS {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Matrix.toLin' (sinaiJacobianInv τ κ) (eigenvecS τ κ) =
      lambdaU (τ * κ) • eigenvecS τ κ := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have hu : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hsq : (Real.sqrt ((τ * κ) * (τ * κ + 4))) ^ 2 =
      (τ * κ) * (τ * κ + 4) := Real.sq_sqrt hu_nonneg
  rw [toLin'_apply]
  ext i
  fin_cases i
  · rw [SinaiHyperbolicErgodicConeFieldBridge.expand_mulVec]
    dsimp [sinaiJacobianInv, eigenvecS, lambdaU, lambdaS]
    nlinarith [hsq]
  · rw [SinaiHyperbolicErgodicConeFieldBridge.expand_mulVec]
    dsimp [sinaiJacobianInv, eigenvecS, lambdaU, lambdaS]
    ring

/-- Cone in the stable/unstable eigenbasis, with the stable coefficient dominant. -/
def stableCone (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  {v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧
    |cu| ≤ α * |cs|}

/-- Strict interior of `stableCone`, excluding its zero-axis boundary. -/
def stableConeInt (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  {v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧
    |cu| < α * |cs| ∧ cs ≠ 0}

/-- The inverse Jacobian maps every nonzero stable-cone vector into the strict
stable cone. -/
theorem strict_stable_cone_invariance {τ κ α : ℝ}
    (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α)
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
      (lambdaS (τ * κ) * cu) • eigenvecU τ κ +
        (lambdaU (τ * κ) * cs) • eigenvecS τ κ := by
    simp only [map_add, map_smul]
    rw [toLin_apply_inv_eigenvecU hτ hκ,
      toLin_apply_inv_eigenvecS hτ hκ]
    rw [smul_smul, smul_smul, mul_comm cu, mul_comm cs]
  refine ⟨lambdaS (τ * κ) * cu, lambdaU (τ * κ) * cs, h_lin, ?_, ?_⟩
  · rw [abs_mul, abs_mul]
    have h_ratio :=
      SinaiHyperbolicErgodicConeFieldBridge.abs_lambdaS_lt_abs_lambdaU hu
    have hcs_pos : 0 < |cs| := abs_pos.mpr hcs_ne
    have h_bound : |lambdaS (τ * κ)| * |cu| ≤
        |lambdaS (τ * κ)| * (α * |cs|) :=
      mul_le_mul_of_nonneg_left h_cone (abs_nonneg _)
    have h_strict : |lambdaS (τ * κ)| * (α * |cs|) <
        |lambdaU (τ * κ)| * (α * |cs|) := by
      exact mul_lt_mul_of_pos_right h_ratio (mul_pos hα hcs_pos)
    calc
      |lambdaS (τ * κ)| * |cu| ≤
          |lambdaS (τ * κ)| * (α * |cs|) := h_bound
      _ < |lambdaU (τ * κ)| * (α * |cs|) := h_strict
      _ = α * (|lambdaU (τ * κ)| * |cs|) := by ring
  · have h_u_ne : lambdaU (τ * κ) ≠ 0 := by
      have hu4 : 0 < (τ * κ) * (τ * κ + 4) := mul_pos hu (by linarith)
      dsimp [lambdaU]
      intro h
      have hroot : -(2 + τ * κ) -
          Real.sqrt ((τ * κ) * (τ * κ + 4)) = 0 := by linarith
      have hsqrt : 0 < Real.sqrt ((τ * κ) * (τ * κ + 4)) :=
        Real.sqrt_pos.mpr hu4
      linarith
    exact mul_ne_zero h_u_ne hcs_ne

/-- The image of the punctured stable cone lies in its strict interior. -/
theorem stable_cone_image_subset_int {τ κ α : ℝ}
    (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α) :
    (Matrix.toLin' (sinaiJacobianInv τ κ)) ''
        (stableCone τ κ α \ {0}) ⊆ stableConeInt τ κ α := by
  rintro w ⟨v, ⟨hv_cone, hv_ne⟩, rfl⟩
  exact strict_stable_cone_invariance hτ hκ hα hv_cone hv_ne

end InfoGeometry.Canonical.SinaiHyperbolicErgodicStableConeBridge
