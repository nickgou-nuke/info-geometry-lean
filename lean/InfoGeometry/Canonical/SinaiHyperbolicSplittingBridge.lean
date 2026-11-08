import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
import InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
import InfoGeometry.Canonical.SinaiHyperbolicErgodicStableConeBridge

namespace InfoGeometry.Canonical.SinaiHyperbolicSplittingBridge

open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge
open InfoGeometry.Canonical.SinaiHyperbolicErgodicStableConeBridge

theorem eigenvec_linear_independent {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    LinearIndependent ℝ ![eigenvecU τ κ, eigenvecS τ κ] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg0 : (g 0) * (1 + lambdaU (τ * κ)) + (g 1) * (1 + lambdaS (τ * κ)) = 0 := by
    have : (∑ i : Fin 2, g i • ![eigenvecU τ κ, eigenvecS τ κ] i) 0 = 0 := by rw [hg, Pi.zero_apply]
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul] at this
    exact this
  have hg1 : (g 0) * (-κ) + (g 1) * (-κ) = 0 := by
    have : (∑ i : Fin 2, g i • ![eigenvecU τ κ, eigenvecS τ κ] i) 1 = 0 := by rw [hg, Pi.zero_apply]
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul] at this
    exact this
  have hg0_eq : g 0 = - g 1 := by
    have : (g 0 + g 1) * (-κ) = 0 := by linarith
    have h_k_ne : -κ ≠ 0 := by linarith
    have : g 0 + g 1 = 0 := by nlinarith
    linarith
  have hg1_zero : g 1 = 0 := by
    have h_sub : g 1 * (lambdaS (τ * κ) - lambdaU (τ * κ)) = 0 := by
      calc g 1 * (lambdaS (τ * κ) - lambdaU (τ * κ))
        _ = (- g 1) * (1 + lambdaU (τ * κ)) + (g 1) * (1 + lambdaS (τ * κ)) := by ring
        _ = (g 0) * (1 + lambdaU (τ * κ)) + (g 1) * (1 + lambdaS (τ * κ)) := by rw [← hg0_eq]
        _ = 0 := hg0
    have hu4 : 0 < (τ * κ) * (τ * κ + 4) := by
      have : 0 < τ * κ := mul_pos hτ hκ
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt ((τ * κ) * (τ * κ + 4)) := Real.sqrt_pos.mpr hu4
    have h_diff_pos : 0 < lambdaS (τ * κ) - lambdaU (τ * κ) := by
      dsimp [lambdaS, lambdaU]
      linarith
    nlinarith
  have hg0_zero : g 0 = 0 := by linarith
  intro i
  fin_cases i
  · exact hg0_zero
  · exact hg1_zero

theorem Eu_isCompl_Es {τ κ : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) :
    IsCompl (Eu τ κ) (Es τ κ) := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, Eu, Es, Submodule.mem_span_singleton, Submodule.mem_span_singleton] at hv
    rcases hv with ⟨⟨cu, rfl⟩, ⟨cs, h_eq⟩⟩
    have h_sum : cu • eigenvecU τ κ + (-cs) • eigenvecS τ κ = 0 := by
      calc cu • eigenvecU τ κ + (-cs) • eigenvecS τ κ
        _ = cu • eigenvecU τ κ - cs • eigenvecS τ κ := by rw [neg_smul, sub_eq_add_neg]
        _ = cs • eigenvecS τ κ - cs • eigenvecS τ κ := by rw [h_eq]
        _ = 0 := by simp
    have h_eq0 : (∑ i : Fin 2, ![cu, -cs] i • ![eigenvecU τ κ, eigenvecS τ κ] i) = 0 := by
      have : cu • eigenvecU τ κ + -(cs • eigenvecS τ κ) = 0 := by rw [← neg_smul]; exact h_sum
      simp [Fin.sum_univ_two, this]
    have hg := eigenvec_linear_independent hτ hκ
    rw [Fintype.linearIndependent_iff] at hg
    have h1 := hg ![cu, -cs] h_eq0
    have hcu : cu = 0 := by
      have h2 := h1 0
      simp at h2
      exact h2
    rw [hcu, zero_smul]
    exact Submodule.zero_mem _
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h_top : Submodule.span ℝ (Set.range ![eigenvecU τ κ, eigenvecS τ κ]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
      rw [hdim]
      have : Module.finrank ℝ (Submodule.span ℝ (Set.range ![eigenvecU τ κ, eigenvecS τ κ])) = Fintype.card (Fin 2) :=
        finrank_span_eq_card (eigenvec_linear_independent hτ hκ)
      exact this
    have hv : v ∈ Submodule.span ℝ (Set.range ![eigenvecU τ κ, eigenvecS τ κ]) := by
      rw [h_top]
      exact Submodule.mem_top
    have h_range : Set.range ![eigenvecU τ κ, eigenvecS τ κ] = ({eigenvecU τ κ} : Set (Fin 2 → ℝ)) ∪ {eigenvecS τ κ} := by
      ext x
      simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · left; rfl
        · right; rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [h_range] at hv
    rw [Eu, Es, ← Submodule.span_union]
    exact hv

theorem cone_disjoint {τ κ α : ℝ} (hτ : 0 < τ) (hκ : 0 < κ) (hα : 0 < α) (hα1 : α < 1) :
    unstableCone τ κ α ∩ stableCone τ κ α = {0} := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h_u, h_s⟩
    rcases h_u with ⟨cu, cs, rfl, h_u_ineq⟩
    rcases h_s with ⟨cu2, cs2, h_eq, h_s_ineq⟩
    have h_sum : (cu - cu2) • eigenvecU τ κ + (cs - cs2) • eigenvecS τ κ = 0 := by
      calc (cu - cu2) • eigenvecU τ κ + (cs - cs2) • eigenvecS τ κ
        _ = cu • eigenvecU τ κ + cs • eigenvecS τ κ - (cu2 • eigenvecU τ κ + cs2 • eigenvecS τ κ) := by
          simp [sub_smul]; abel
        _ = cu • eigenvecU τ κ + cs • eigenvecS τ κ - (cu • eigenvecU τ κ + cs • eigenvecS τ κ) := by rw [h_eq]
        _ = 0 := sub_self _
    have h_eq0 : (∑ i : Fin 2, ![cu - cu2, cs - cs2] i • ![eigenvecU τ κ, eigenvecS τ κ] i) = 0 := by
      have : (cu - cu2) • eigenvecU τ κ + (cs - cs2) • eigenvecS τ κ = 0 := h_sum
      simp [Fin.sum_univ_two, this]
    have hg := eigenvec_linear_independent hτ hκ
    rw [Fintype.linearIndependent_iff] at hg
    have h1 := hg ![cu - cu2, cs - cs2] h_eq0
    have hcu : cu - cu2 = 0 := by have h2 := h1 0; simp at h2; exact h2
    have hcs : cs - cs2 = 0 := by have h2 := h1 1; simp at h2; exact h2
    have cu_eq : cu = cu2 := sub_eq_zero.mp hcu
    have cs_eq : cs = cs2 := sub_eq_zero.mp hcs
    rw [cu_eq, cs_eq] at h_u_ineq
    have h3 : |cs2| ≤ α^2 * |cs2| := by
      calc |cs2| ≤ α * |cu2| := h_u_ineq
        _ ≤ α * (α * |cs2|) := mul_le_mul_of_nonneg_left h_s_ineq (le_of_lt hα)
        _ = α^2 * |cs2| := by ring
    have h4 : |cs2| * (1 - α^2) ≤ 0 := by
      calc |cs2| * (1 - α^2) = |cs2| - α^2 * |cs2| := by ring
        _ ≤ 0 := sub_nonpos_of_le h3
    have h_alpha_sq : 0 < 1 - α^2 := by
      have : α^2 < 1^2 := by
        nlinarith
      linarith
    have hcs2_zero : |cs2| ≤ 0 := nonpos_of_mul_nonpos_left h4 h_alpha_sq
    have cs2_zero : cs2 = 0 := by
      have : |cs2| = 0 := le_antisymm hcs2_zero (abs_nonneg _)
      exact abs_eq_zero.mp this
    have cu2_zero : cu2 = 0 := by
      rw [cs2_zero] at h_s_ineq
      have h5 : |cu2| ≤ α * |(0 : ℝ)| := h_s_ineq
      have h6 : |cu2| ≤ 0 := by
        calc |cu2| ≤ α * |(0 : ℝ)| := h5
          _ = 0 := by simp
      exact abs_nonpos_iff.mp h6
    have cu_zero : cu = 0 := by rw [cu_eq, cu2_zero]
    have cs_zero : cs = 0 := by rw [cs_eq, cs2_zero]
    rw [cu_zero, cs_zero]
    simp
  · rintro rfl
    have hz : (0 : ℝ) • eigenvecU τ κ + (0 : ℝ) • eigenvecS τ κ = 0 := by simp
    constructor
    · exact ⟨0, 0, hz.symm, by simp⟩
    · exact ⟨0, 0, hz.symm, by simp⟩

end InfoGeometry.Canonical.SinaiHyperbolicSplittingBridge
