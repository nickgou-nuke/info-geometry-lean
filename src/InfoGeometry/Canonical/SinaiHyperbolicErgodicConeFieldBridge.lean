import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Matrix
open scoped Matrix

namespace InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

def sinaiJacobian (τ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1 + τ * κ), -τ;
     -κ,           -1]

noncomputable def lambdaU (u : ℝ) : ℝ :=
  (-(2 + u) - Real.sqrt (u * (u + 4))) / 2

noncomputable def lambdaS (u : ℝ) : ℝ :=
  (-(2 + u) + Real.sqrt (u * (u + 4))) / 2

noncomputable def eigenvecU (τ κ : ℝ) : Fin 2 → ℝ :=
  ![1 + lambdaU (τ * κ), -κ]

noncomputable def eigenvecS (τ κ : ℝ) : Fin 2 → ℝ :=
  ![1 + lambdaS (τ * κ), -κ]

noncomputable def Eu (τ κ : ℝ) : Submodule ℝ (Fin 2 → ℝ) :=
  Submodule.span ℝ {eigenvecU τ κ}

noncomputable def Es (τ κ : ℝ) : Submodule ℝ (Fin 2 → ℝ) :=
  Submodule.span ℝ {eigenvecS τ κ}

theorem char_poly_root_u {u : ℝ} (hu : 0 ≤ u * (u + 4)) :
    (lambdaU u)^2 + (2 + u) * (lambdaU u) + 1 = 0 := by
  dsimp [lambdaU]
  have hsq : (Real.sqrt (u * (u + 4)))^2 = u * (u + 4) := Real.sq_sqrt hu
  linear_combination 1/4 * hsq

theorem char_poly_root_s {u : ℝ} (hu : 0 ≤ u * (u + 4)) :
    (lambdaS u)^2 + (2 + u) * (lambdaS u) + 1 = 0 := by
  dsimp [lambdaS]
  have hsq : (Real.sqrt (u * (u + 4)))^2 = u * (u + 4) := Real.sq_sqrt hu
  linear_combination 1/4 * hsq

theorem eigenvecU_ne_zero {τ κ : ℝ} (hκ : 0 < κ) : eigenvecU τ κ ≠ 0 := by
  intro h
  have h1 : eigenvecU τ κ 1 = 0 := by rw [h, Pi.zero_apply]
  dsimp [eigenvecU] at h1
  linarith

theorem eigenvecS_ne_zero {τ κ : ℝ} (hκ : 0 < κ) : eigenvecS τ κ ≠ 0 := by
  intro h
  have h1 : eigenvecS τ κ 1 = 0 := by rw [h, Pi.zero_apply]
  dsimp [eigenvecS] at h1
  linarith

lemma expand_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
  mulVec A v i = A i 0 * v 0 + A i 1 * v 1 := by
  rw [mulVec, dotProduct, Fin.sum_univ_two]

theorem sinaiJacobian_mulVec_eigenvecU {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiJacobian τ κ) (eigenvecU τ κ) = lambdaU (τ * κ) • (eigenvecU τ κ) := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hpoly := char_poly_root_u hu_nonneg
  ext i
  fin_cases i
  · rw [expand_mulVec]
    dsimp [sinaiJacobian, eigenvecU]
    linear_combination -hpoly
  · rw [expand_mulVec]
    dsimp [sinaiJacobian, eigenvecU]
    ring

theorem sinaiJacobian_mulVec_eigenvecS {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    mulVec (sinaiJacobian τ κ) (eigenvecS τ κ) = lambdaS (τ * κ) • (eigenvecS τ κ) := by
  have hu_nonneg : 0 ≤ (τ * κ) * (τ * κ + 4) := by
    have : 0 < τ * κ := mul_pos hτ hκ
    positivity
  have hpoly := char_poly_root_s hu_nonneg
  ext i
  fin_cases i
  · rw [expand_mulVec]
    dsimp [sinaiJacobian, eigenvecS]
    linear_combination -hpoly
  · rw [expand_mulVec]
    dsimp [sinaiJacobian, eigenvecS]
    ring

theorem toLin_apply_eigenvecU {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Matrix.toLin' (sinaiJacobian τ κ) (eigenvecU τ κ) = lambdaU (τ * κ) • eigenvecU τ κ := by
  rw [toLin'_apply, sinaiJacobian_mulVec_eigenvecU hτ hκ]

theorem toLin_apply_eigenvecS {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Matrix.toLin' (sinaiJacobian τ κ) (eigenvecS τ κ) = lambdaS (τ * κ) • eigenvecS τ κ := by
  rw [toLin'_apply, sinaiJacobian_mulVec_eigenvecS hτ hκ]

theorem Eu_invariant {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Submodule.map (Matrix.toLin' (sinaiJacobian τ κ)) (Eu τ κ) ≤ Eu τ κ := by
  rw [Eu, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  obtain rfl : y = eigenvecU τ κ := hy
  rw [toLin_apply_eigenvecU hτ hκ]
  exact Submodule.smul_mem (Eu τ κ) (lambdaU (τ * κ)) (Submodule.mem_span_singleton_self _)

theorem Es_invariant {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Submodule.map (Matrix.toLin' (sinaiJacobian τ κ)) (Es τ κ) ≤ Es τ κ := by
  rw [Es, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  obtain rfl : y = eigenvecS τ κ := hy
  rw [toLin_apply_eigenvecS hτ hκ]
  exact Submodule.smul_mem (Es τ κ) (lambdaS (τ * κ)) (Submodule.mem_span_singleton_self _)

theorem finrank_Eu {τ κ : ℝ} (hκ : 0 < κ) :
    Module.finrank ℝ (Eu τ κ) = 1 := by
  rw [Eu]
  exact finrank_span_singleton (eigenvecU_ne_zero hκ)

theorem finrank_Es {τ κ : ℝ} (hκ : 0 < κ) :
    Module.finrank ℝ (Es τ κ) = 1 := by
  rw [Es]
  exact finrank_span_singleton (eigenvecS_ne_zero hκ)

theorem Eu_le_eigenspace {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    Eu τ κ ≤ Module.End.eigenspace (Matrix.toLin' (sinaiJacobian τ κ)) (lambdaU (τ * κ)) := by
  rw [Eu, Submodule.span_le]
  intro x hx
  obtain rfl : x = eigenvecU τ κ := hx
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
  exact toLin_apply_eigenvecU hτ hκ

def unstableCone (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  { v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧ |cs| ≤ α * |cu| }

def unstableConeInt (τ κ α : ℝ) : Set (Fin 2 → ℝ) :=
  { v | ∃ cu cs : ℝ, v = cu • eigenvecU τ κ + cs • eigenvecS τ κ ∧ |cs| < α * |cu| ∧ cu ≠ 0 }

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

  rw [h_abs_s, h_abs_u]; linarith

theorem strict_cone_invariance {τ κ α : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α)
    {v : Fin 2 → ℝ} (hv : v ∈ unstableCone τ κ α) (hv_ne : v ≠ 0) :
    Matrix.toLin' (sinaiJacobian τ κ) v ∈ unstableConeInt τ κ α := by
  rcases hv with ⟨cu, cs, rfl, h_cone⟩
  have hu : 0 < τ * κ := mul_pos hτ hκ

  have hcu_ne : cu ≠ 0 := by
    intro hcu
    have hcs_zero : cs = 0 := by
      have hle : |cs| ≤ α * |cu| := h_cone
      rw [hcu, abs_zero, mul_zero] at hle
      exact abs_nonpos_iff.mp hle
    subst hcu
    subst hcs_zero
    simp only [zero_smul, add_zero] at hv_ne
    exact False.elim (hv_ne rfl)

  let L := Matrix.toLin' (sinaiJacobian τ κ)
  have h_lin : L (cu • eigenvecU τ κ + cs • eigenvecS τ κ) =
      (lambdaU (τ * κ) * cu) • eigenvecU τ κ + (lambdaS (τ * κ) * cs) • eigenvecS τ κ := by
    simp only [map_add, map_smul]
    rw [toLin_apply_eigenvecU hτ hκ, toLin_apply_eigenvecS hτ hκ]
    rw [smul_smul, smul_smul, mul_comm cu, mul_comm cs]

  use lambdaU (τ * κ) * cu, lambdaS (τ * κ) * cs
  refine ⟨h_lin, ?_, ?_⟩
  · rw [abs_mul, abs_mul]
    have h_ratio := abs_lambdaS_lt_abs_lambdaU hu
    have h_cu_pos : 0 < |cu| := abs_pos.mpr hcu_ne
    have h_bound : |lambdaS (τ * κ)| * |cs| ≤ |lambdaS (τ * κ)| * (α * |cu|) :=
      mul_le_mul_of_nonneg_left h_cone (abs_nonneg _)
    have h_strict : |lambdaS (τ * κ)| * (α * |cu|) < |lambdaU (τ * κ)| * (α * |cu|) := by
      have h_coeff : 0 < α * |cu| := mul_pos hα h_cu_pos
      exact mul_lt_mul_of_pos_right h_ratio h_coeff
    calc
      |lambdaS (τ * κ)| * |cs| ≤ |lambdaS (τ * κ)| * (α * |cu|) := h_bound
      _ < |lambdaU (τ * κ)| * (α * |cu|) := h_strict
      _ = α * (|lambdaU (τ * κ)| * |cu|) := by ring
  · have h_u_ne : lambdaU (τ * κ) ≠ 0 := by
      have hu4 : 0 < (τ * κ) * (τ * κ + 4) := mul_pos hu (by linarith)
      dsimp [lambdaU]
      intro h
      have : -(2 + τ * κ) - Real.sqrt ((τ * κ) * (τ * κ + 4)) = 0 := by linarith
      have : 0 < Real.sqrt ((τ * κ) * (τ * κ + 4)) := Real.sqrt_pos.mpr hu4
      linarith
    exact mul_ne_zero h_u_ne hcu_ne

theorem cone_image_subset_int {τ κ α : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α) :
    (Matrix.toLin' (sinaiJacobian τ κ)) '' (unstableCone τ κ α \ {0}) ⊆ unstableConeInt τ κ α := by
  rintro w ⟨v, ⟨hv_cone, hv_ne⟩, rfl⟩
  exact strict_cone_invariance hτ hκ hα hv_cone hv_ne

end InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
