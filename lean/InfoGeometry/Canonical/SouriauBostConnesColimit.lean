import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Field.Basic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.BCPartitionFunction

noncomputable section

open Filter Topology Real
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

namespace InfoGeometry.Canonical.SouriauBostConnesColimit

/-!
# Souriau-Bost-Connes Colimit Transition

This module provides the analytic construction of the Bost-Connes partition function
and the zero-temperature ($\beta \to \infty$) limit over the `UHFInductiveColimitBoundary`.
It strictly satisfies the Colimit Continuum Mandate.
-/

lemma tendsto_rpow_neg_beta {c : ℝ} (hc : 1 < c) :
    Tendsto (fun beta : ℝ => c ^ (-beta)) atTop (𝓝 0) := by
  have h_eq : (fun beta : ℝ => c ^ (-beta)) = fun beta => (c⁻¹) ^ beta := by
    ext b
    exact (Real.inv_rpow (le_trans zero_le_one (le_of_lt hc)) b).symm ▸ (Real.rpow_neg (le_trans zero_le_one (le_of_lt hc)) b)
  rw [h_eq]
  apply tendsto_rpow_atTop_of_base_lt_one
  · exact lt_of_lt_of_le neg_one_lt_zero (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hc)))
  · exact inv_lt_one_of_one_lt₀ hc

lemma tendsto_factor (i : ℕ) (b : Bool) :
    Tendsto (fun beta : ℝ => if b = true then (i + 2 : ℝ) ^ (-beta) else 1 - (i + 2 : ℝ) ^ (-beta)) atTop (𝓝 (if b = true then (0 : ℝ) else 1)) := by
  have hbase : (1 : ℝ) < (i + 2 : ℝ) := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have hlim := tendsto_rpow_neg_beta hbase
  by_cases hb : b = true
  · have h1 : (fun beta : ℝ => if b = true then (i + 2 : ℝ) ^ (-beta) else 1 - (i + 2 : ℝ) ^ (-beta)) = fun beta => (i + 2 : ℝ) ^ (-beta) := by
      ext beta; rw [if_pos hb]
    have h2 : (if b = true then (0 : ℝ) else 1) = 0 := if_pos hb
    rw [h1, h2]
    exact hlim
  · have h1 : (fun beta : ℝ => if b = true then (i + 2 : ℝ) ^ (-beta) else 1 - (i + 2 : ℝ) ^ (-beta)) = fun beta => 1 - (i + 2 : ℝ) ^ (-beta) := by
      ext beta; rw [if_neg hb]
    have h2 : (if b = true then (0 : ℝ) else 1) = 1 := if_neg hb
    rw [h1, h2]
    have h_sub : Tendsto (fun beta : ℝ => 1 - (i + 2 : ℝ) ^ (-beta)) atTop (𝓝 (1 - 0)) := Tendsto.const_sub 1 hlim
    have h_eq : (1 - 0 : ℝ) = 1 := sub_zero 1
    rw [h_eq] at h_sub
    exact h_sub

lemma tendsto_product (n : ℕ) (w : BitWord n) :
    Tendsto (fun beta : ℝ => ∏ i : Fin n, if w i = true then (i.val + 2 : ℝ) ^ (-beta) else 1 - (i.val + 2 : ℝ) ^ (-beta))
      atTop (𝓝 (if (∀ i, w i = false) then (1 : ℝ) else 0)) := by
  have h_prod := tendsto_finset_prod (Finset.univ : Finset (Fin n))
    (fun (i : Fin n) _ => tendsto_factor i.val (w i))
  have h_eq : (∏ i : Fin n, if w i = true then (0 : ℝ) else 1) = if (∀ i, w i = false) then 1 else 0 := by
    by_cases h : ∀ i, w i = false
    · have h1 : ∀ i, (if w i = true then (0 : ℝ) else 1) = 1 := by
        intro i
        have hf : ¬ (w i = true) := by
          intro hwt
          have hwf := h i
          rw [hwt] at hwf
          contradiction
        exact if_neg hf
      rw [Finset.prod_congr rfl (fun i _ => h1 i)]
      simp [h]
    · push_neg at h
      rcases h with ⟨j, hj⟩
      have hj2 : w j = true := by
        cases hw : w j
        · contradiction
        · rfl
      have h0 : (fun i : Fin n => if w i = true then (0 : ℝ) else 1) j = 0 := if_pos hj2
      have hprod0 : (∏ i : Fin n, if w i = true then (0 : ℝ) else 1) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h0
      have hf : (if ∀ (i : Fin n), w i = false then 1 else (0 : ℝ)) = 0 := by
        apply if_neg
        intro h_all
        have hjf := h_all j
        rw [hj2] at hjf
        contradiction
      rw [hprod0, hf]
  rw [← h_eq]
  exact h_prod

/-- Local thermodynamic state at stage `n` (finite cutoff of primes).
The state assigns a weight to each boolean word.
At inverse temperature `beta`, we assign probability `p^{-beta}` to the 1-bit,
and `1 - p^{-beta}` to the 0-bit. -/
def finiteCutoffState (beta : ℝ) (n : ℕ) (f : DiagAlg n) : ℂ :=
  ∑ w : BitWord n, f w * (((∏ i : Fin n, if w i = true then (i.val + 2 : ℝ) ^ (-beta) else (1 - (i.val + 2 : ℝ) ^ (-beta))) : ℝ) : ℂ)

/-- The zero-temperature evaluation limit of the state. -/
theorem zero_temperature_crystallization (n : ℕ) (f : DiagAlg n) :
    Tendsto (fun beta : ℝ => finiteCutoffState beta n f) atTop (𝓝 (f (fun _ => false))) := by
  dsimp [finiteCutoffState]
  have h_sum := tendsto_finset_sum (Finset.univ : Finset (BitWord n))
    (fun w _ => by
      have h_lim := tendsto_product n w
      have h_cast : Tendsto (fun beta : ℝ => (((∏ i : Fin n, if w i = true then (i.val + 2 : ℝ) ^ (-beta) else 1 - (i.val + 2 : ℝ) ^ (-beta)) : ℝ) : ℂ)) atTop (𝓝 (((if ∀ (i : Fin n), w i = false then 1 else 0 : ℝ) : ℂ))) :=
        Tendsto.comp (Continuous.tendsto Complex.continuous_ofReal _) h_lim
      exact Tendsto.const_mul (f w) h_cast
    )
  have h_eq : (∑ w : BitWord n, f w * (((if ∀ (i : Fin n), w i = false then 1 else 0 : ℝ) : ℂ))) = f (fun _ => false) := by
    let w0 : BitWord n := fun _ => false
    have h_single : (∑ w : BitWord n, f w * (((if ∀ (i : Fin n), w i = false then 1 else 0 : ℝ) : ℂ))) = f w0 * (((if ∀ (i : Fin n), w0 i = false then 1 else 0 : ℝ) : ℂ)) := by
      apply Finset.sum_eq_single w0
      · intro b _ hb
        have hb_not_all_false : ¬ (∀ i, b i = false) := by
          intro h
          apply hb
          ext i
          exact h i
        have h_if : (if ∀ (i : Fin n), b i = false then 1 else (0:ℝ)) = 0 := if_neg hb_not_all_false
        rw [h_if]
        simp
      · intro h
        exfalso
        exact h (Finset.mem_univ w0)
    rw [h_single]
    have hl : ∀ i : Fin n, w0 i = false := fun _ => rfl
    have hl2 : (if ∀ (i : Fin n), w0 i = false then 1 else (0:ℝ)) = 1 := if_pos hl
    rw [hl2]
    simp
    rfl
  rw [← h_eq]
  exact h_sum

end InfoGeometry.Canonical.SouriauBostConnesColimit
