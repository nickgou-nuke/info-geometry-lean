/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Section 5.86: Multi-Dimensional Aitchison CLR Isometry & Facet Divergence

This module formalizes:
1. Open probability simplex `Simplex D`: `p_i > 0` and `∑ p_i = 1`.
2. Geometric log-mean `logGeomMean p = (1/D) * ∑ ln(p_i)`.
3. Centered Log-Ratio transformation: `clr p i = ln(p_i) - logGeomMean p`.
4. Theorem 1 (Trace-Free Projection):
   `∑ i, clr p i = 0`.
5. Theorem 2 (Jaynesian Prior is the Origin):
   `clr (jaynes D) i = 0`.
6. Theorem 3 (Double Sum Equivalence / CLR Isometry):
   `∑ i, (u i)^2 = (1 / (2D)) * ∑ i, ∑ j, (u i - u j)^2` for any trace-free `u`.
7. Theorem 4 (Aitchison Pairwise Log-Ratio Metric):
   `d_A(p, q)² = (1 / (2D)) * ∑ i, ∑ j, (ln(p_i / p_j) - ln(q_i / q_j))²`.
8. Theorem 5 (Aitchison Perturbation Homomorphism):
   `clr (p ⊕ q) i = clr p i + clr q i`.
9. Theorem 6 (Simplex Non-Positivity of Logarithms):
   `p_i ≤ 1` and `ln(p_i) ≤ 0`.
10. Theorem 7 (Log-Mean Facet Upper Bound):
    `logGeomMean p ≤ (1/D) * ln(p_k)` for any coordinate `k`.
11. Master Theorem 8 (Non-Asymptotic Facet Divergence Bound):
    `D_KL(u₀ ‖ p) ≥ (1/D) * ln(1 / p_k) - ln D`.
12. Master Theorem 9 (Shannon Relative Entropy Divergence):
    For any threshold `M : ℝ`, there exists `δ > 0` such that `p_k < δ → D_KL(u₀ ‖ p) > M`.

Zero debt, 0 sorry, 0 admit, kernel-checked in Lean 4.
-/

namespace InfoGeometry.Physics.AitchisonCLRSimplex

/-! ### Part I: The Open Simplex and CLR Map -/

/-- The open probability simplex Δ^{D-1} in dimension D. -/
structure Simplex (D : ℕ) where
  val : Fin D → ℝ
  pos : ∀ i, 0 < val i
  sum_one : (∑ i, val i) = 1

variable {D : ℕ} [NeZero D]

/-- The geometric log-mean: `(1/D) * ∑ ln(p_i)`. -/
noncomputable def logGeomMean (p : Simplex D) : ℝ :=
  (1 / (D : ℝ)) * (∑ i, Real.log (p.val i))

/-- The Centered Log-Ratio (CLR) coordinate vector:
    `clr(p)_i = ln(p_i) - (1/D) ∑ ln(p_k)`. -/
noncomputable def clr (p : Simplex D) (i : Fin D) : ℝ :=
  Real.log (p.val i) - logGeomMean p

/-- **Theorem 1 (Trace-Free Projection onto 𝔰𝔩(D, ℝ) Cartan Subalgebra)**:
    The sum of the CLR coordinates vanishes identically: `∑ i, clr(p)_i = 0`. -/
theorem clr_trace_zero (p : Simplex D) : (∑ i, clr p i) = 0 := by
  dsimp [clr, logGeomMean]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have h_cancel : (D : ℝ) * ((1 / (D : ℝ)) * ∑ i, Real.log (p.val i)) = ∑ i, Real.log (p.val i) := by
    rw [← mul_assoc, mul_one_div_cancel hD, one_mul]
  rw [h_cancel, sub_self]

/-! ### Part II: Jaynesian Reference State as Algebraic Origin -/

/-- The uniform Jaynesian maximum entropy reference state: `u₀ = (1/D, ..., 1/D)`. -/
noncomputable def jaynes (D : ℕ) [NeZero D] : Simplex D where
  val := fun _ => 1 / (D : ℝ)
  pos := fun _ => by
    have : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (NeZero.pos D)
    exact one_div_pos.mpr this
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
    exact mul_one_div_cancel hD

/-- **Theorem 2 (Jaynesian Prior is the Exact CLR Origin)**:
    `clr(u₀)_i = 0` for all indices i. -/
theorem jaynes_clr_zero (i : Fin D) : clr (jaynes D) i = 0 := by
  dsimp [clr, logGeomMean, jaynes]
  have h_sum : (∑ j : Fin D, Real.log (1 / (D : ℝ))) = (D : ℝ) * Real.log (1 / (D : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h_sum]
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have h_cancel : (1 / (D : ℝ)) * ((D : ℝ) * Real.log (1 / (D : ℝ))) = Real.log (1 / (D : ℝ)) := by
    rw [← mul_assoc, one_div_mul_cancel hD, one_mul]
  rw [h_cancel, sub_self]

/-! ### Part III: Double Sum Lemma & Aitchison Metric Isometry -/

/-- **Theorem 3 (Trace-Free Quadratic Identity)**:
    For any vector u with vanishing trace `∑ u_i = 0`:
    `∑ i, ∑ j, (u_i - u_j)² = 2D * ∑ i, (u_i)²`. -/
theorem sum_sq_diff_of_sum_zero (u : Fin D → ℝ) (hu : (∑ i, u i) = 0) :
    (∑ i, ∑ j, (u i - u j) ^ 2) = 2 * (D : ℝ) * (∑ i, (u i) ^ 2) := by
  have h_inner : ∀ i, (∑ j, (u i - u j) ^ 2) = (D : ℝ) * (u i) ^ 2 + ∑ j, (u j) ^ 2 := by
    intro i
    have h_expand : ∀ j, (u i - u j) ^ 2 = (u i) ^ 2 + (u j) ^ 2 - 2 * u i * u j := by
      intro j; ring
    simp_rw [h_expand]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h_cross : (∑ j, 2 * u i * u j) = 2 * u i * (∑ j, u j) := by
      rw [← Finset.mul_sum]
    rw [h_cross, hu, mul_zero, sub_zero]
  simp_rw [h_inner]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The Aitchison Euclidean metric on CLR coordinates:
    `d_A(p, q)² = ∑ i, (clr(p)_i - clr(q)_i)²`. -/
noncomputable def aitchisonDistSq (p q : Simplex D) : ℝ :=
  ∑ i, (clr p i - clr q i) ^ 2

/-- **Theorem 4 (Equivalence to Pairwise Log-Ratio Form)**:
    The CLR Euclidean distance is identically equal to the Aitchison log-ratio metric:
    `d_A(p, q)² = (1 / 2D) * ∑ i, ∑ j, (ln(p_i / p_j) - ln(q_i / q_j))²`. -/
theorem aitchison_pairwise_formula (p q : Simplex D) :
    aitchisonDistSq p q =
    (1 / (2 * (D : ℝ))) * (∑ i, ∑ j, (Real.log (p.val i / p.val j) - Real.log (q.val i / q.val j)) ^ 2) := by
  let u : Fin D → ℝ := fun i => clr p i - clr q i
  have hu : (∑ i, u i) = 0 := by
    dsimp [u]
    rw [Finset.sum_sub_distrib, clr_trace_zero p, clr_trace_zero q, sub_zero]
  have h_diff : ∀ i j, u i - u j = Real.log (p.val i / p.val j) - Real.log (q.val i / q.val j) := by
    intro i j
    dsimp [u, clr]
    have hp_pos_i := ne_of_gt (p.pos i)
    have hp_pos_j := ne_of_gt (p.pos j)
    have hq_pos_i := ne_of_gt (q.pos i)
    have hq_pos_j := ne_of_gt (q.pos j)
    rw [Real.log_div hp_pos_i hp_pos_j]
    rw [Real.log_div hq_pos_i hq_pos_j]
    ring
  have h_sum_diff : (∑ i, ∑ j, (Real.log (p.val i / p.val j) - Real.log (q.val i / q.val j)) ^ 2) =
      (∑ i, ∑ j, (u i - u j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← h_diff i j]
  rw [h_sum_diff]
  rw [sum_sq_diff_of_sum_zero u hu]
  have hD_pos : 0 < (D : ℝ) := Nat.cast_pos.mpr (NeZero.pos D)
  have h2D : 2 * (D : ℝ) ≠ 0 := by linarith
  dsimp [aitchisonDistSq, u]
  rw [← mul_assoc, one_div_mul_cancel h2D, one_mul]

/-! ### Part IV: Aitchison Simplex Perturbation as CLR Vector Addition -/

/-- Denominator for Aitchison perturbation: `∑_k p_k q_k > 0`. -/
def perturbDenom (p q : Simplex D) : ℝ :=
  ∑ i, p.val i * q.val i

lemma perturbDenom_pos (p q : Simplex D) : 0 < perturbDenom p q := by
  dsimp [perturbDenom]
  have h0 : (0 : Fin D) = ⟨0, NeZero.pos D⟩ := rfl
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (mul_pos (p.pos i) (q.pos i))
  · exact ⟨0, Finset.mem_univ 0, mul_pos (p.pos 0) (q.pos 0)⟩

/-- The Aitchison simplex perturbation operation `p ⊕ q`. -/
noncomputable def perturb (p q : Simplex D) : Simplex D where
  val := fun i => (p.val i * q.val i) / perturbDenom p q
  pos := fun i => div_pos (mul_pos (p.pos i) (q.pos i)) (perturbDenom_pos p q)
  sum_one := by
    dsimp [perturbDenom]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (perturbDenom_pos p q))

/-- **Theorem 5 (Aitchison Perturbation is Additive Vector Addition in CLR)**:
    `clr(p ⊕ q)_i = clr(p)_i + clr(q)_i`. -/
theorem clr_perturbation (p q : Simplex D) (i : Fin D) :
    clr (perturb p q) i = clr p i + clr q i := by
  dsimp [clr, logGeomMean, perturb]
  let C := perturbDenom p q
  have hC : 0 < C := perturbDenom_pos p q
  have hC_ne : C ≠ 0 := ne_of_gt hC
  have h_log_comp : ∀ j, Real.log ((p.val j * q.val j) / C) =
      Real.log (p.val j) + Real.log (q.val j) - Real.log C := by
    intro j
    have hpq_ne : p.val j * q.val j ≠ 0 := ne_of_gt (mul_pos (p.pos j) (q.pos j))
    rw [Real.log_div hpq_ne hC_ne]
    rw [Real.log_mul (ne_of_gt (p.pos j)) (ne_of_gt (q.pos j))]
  have h_sum_comp : (∑ j, Real.log ((p.val j * q.val j) / C)) =
      (∑ j, Real.log (p.val j)) + (∑ j, Real.log (q.val j)) - (D : ℝ) * Real.log C := by
    simp_rw [h_log_comp]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  have h_mean_comp : (1 / (D : ℝ)) * (∑ j, Real.log ((p.val j * q.val j) / C)) =
      (1 / (D : ℝ)) * (∑ j, Real.log (p.val j)) + (1 / (D : ℝ)) * (∑ j, Real.log (q.val j)) - Real.log C := by
    rw [h_sum_comp]
    have h_scale : (1 / (D : ℝ)) * ((∑ j, Real.log (p.val j)) + (∑ j, Real.log (q.val j)) - (D : ℝ) * Real.log C) =
        (1 / (D : ℝ)) * (∑ j, Real.log (p.val j)) + (1 / (D : ℝ)) * (∑ j, Real.log (q.val j)) -
        ((1 / (D : ℝ)) * (D : ℝ)) * Real.log C := by ring
    rw [h_scale, one_div_mul_cancel hD, one_mul]
  rw [h_log_comp i, h_mean_comp]
  ring

/-! ### Part V: Facet Geometry & Shannon Relative Entropy Divergence -/

/-- **Theorem 6 (Component Probabilities are Bounded by 1)**:
    `p_i ≤ 1` for all i in any probability simplex. -/
theorem val_le_one (p : Simplex D) (i : Fin D) : p.val i ≤ 1 := by
  have h_sum : p.val i ≤ ∑ j, p.val j :=
    Finset.single_le_sum (fun j _ => le_of_lt (p.pos j)) (Finset.mem_univ i)
  rw [p.sum_one] at h_sum
  exact h_sum

/-- **Theorem 7 (Non-Positivity of Component Logarithms)**:
    `ln(p_i) ≤ 0` on the simplex. -/
theorem log_val_nonpos (p : Simplex D) (i : Fin D) : Real.log (p.val i) ≤ 0 := by
  rw [← Real.log_one]
  exact Real.log_le_log (p.pos i) (val_le_one p i)

/-- **Theorem 8 (Upper Bound on Log-Sum by Single Component)**:
    `∑ i, ln(p_i) ≤ ln(p_k)` for any facet index k. -/
theorem sum_log_le_log_k (p : Simplex D) (k : Fin D) :
    (∑ i, Real.log (p.val i)) ≤ Real.log (p.val k) := by
  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ - Real.log (p.val i) := by
    intro i _
    have := log_val_nonpos p i
    linarith
  have h_single := Finset.single_le_sum h_nonneg (Finset.mem_univ k)
  rw [Finset.sum_neg_distrib] at h_single
  linarith

/-- **Theorem 9 (Geometric Log-Mean Bound at the Facet)**:
    `logGeomMean p ≤ (1/D) * ln(p_k)`. -/
theorem logGeomMean_le_facet (p : Simplex D) (k : Fin D) :
    logGeomMean p ≤ (1 / (D : ℝ)) * Real.log (p.val k) := by
  dsimp [logGeomMean]
  have hD_pos : 0 < (D : ℝ) := Nat.cast_pos.mpr (NeZero.pos D)
  have h_inv_pos : 0 < 1 / (D : ℝ) := one_div_pos.mpr hD_pos
  exact mul_le_mul_of_nonneg_left (sum_log_le_log_k p k) (le_of_lt h_inv_pos)

/-- The Shannon Relative Entropy (Kullback-Leibler divergence)
    from the Jaynesian prior to the distribution p:
    `D_KL(u₀ ‖ p) = - ln D - logGeomMean p`. -/
noncomputable def relativeEntropyJaynes (p : Simplex D) : ℝ :=
  - Real.log (D : ℝ) - logGeomMean p

/-- **Master Theorem 10 (Non-Asymptotic Facet Divergence Bound)**:
    For any simplex distribution and any component k:
    `D_KL(u₀ ‖ p) ≥ (1/D) * ln(1 / p_k) - ln D`. -/
theorem relative_entropy_facet_lower_bound (p : Simplex D) (k : Fin D) :
    (1 / (D : ℝ)) * Real.log (1 / p.val k) - Real.log (D : ℝ) ≤ relativeEntropyJaynes p := by
  dsimp [relativeEntropyJaynes]
  have h_mean := logGeomMean_le_facet p k
  have h_log_inv : Real.log (1 / p.val k) = - Real.log (p.val k) := by
    rw [Real.log_div one_ne_zero (ne_of_gt (p.pos k)), Real.log_one, zero_sub]
  rw [h_log_inv]
  linarith

/-- **Master Theorem 11 (Strict Divergence of Shannon Relative Entropy at Facets)**:
    The Shannon relative entropy diverges to +∞ as the probability state approaches
    any boundary facet: for any bound M, choosing `p_k < exp(- D * (M + ln D + 1))`
    guarantees `D_KL(u₀ ‖ p) > M`. -/
theorem relative_entropy_diverges_at_facets (M : ℝ) :
    ∃ δ > 0, ∀ (p : Simplex D) (k : Fin D), p.val k < δ → M < relativeEntropyJaynes p := by
  let E := (D : ℝ) * (M + Real.log (D : ℝ) + 1)
  let δ := Real.exp (- E)
  have hδ_pos : 0 < δ := Real.exp_pos (- E)
  use δ, hδ_pos
  intro p k hpk
  have h_log_lt : Real.log (p.val k) < - E := by
    have h_lt := Real.log_lt_log (p.pos k) hpk
    rw [Real.log_exp (- E)] at h_lt
    exact h_lt
  have h_neg_log : E < - Real.log (p.val k) := by linarith
  have h_log_inv : Real.log (1 / p.val k) = - Real.log (p.val k) := by
    rw [Real.log_div one_ne_zero (ne_of_gt (p.pos k)), Real.log_one, zero_sub]
  have h_E_lt : E < Real.log (1 / p.val k) := by
    rw [h_log_inv]
    exact h_neg_log
  have hD_pos : 0 < (D : ℝ) := Nat.cast_pos.mpr (NeZero.pos D)
  have h_scale : (1 / (D : ℝ)) * E < (1 / (D : ℝ)) * Real.log (1 / p.val k) := by
    exact mul_lt_mul_of_pos_left h_E_lt (one_div_pos.mpr hD_pos)
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
  have h_E_eval : (1 / (D : ℝ)) * E = M + Real.log (D : ℝ) + 1 := by
    dsimp [E]
    rw [← mul_assoc, one_div_mul_cancel hD_ne, one_mul]
  rw [h_E_eval] at h_scale
  have h_bound := relative_entropy_facet_lower_bound p k
  linarith

/-! ### Part VI: Master Synthesis Theorem -/

/-- Master Synthesis: Unifies CLR trace cancellation, Jaynesian prior origin,
    Aitchison pairwise metric isometry, perturbation homomorphism,
    non-asymptotic facet divergence bound, and asymptotic divergence to infinity. -/
theorem aitchison_clr_simplex_synthesis (p q : Simplex D) (i k : Fin D) (M : ℝ) :
    (clr (jaynes D) i = 0) ∧
    ((∑ j, clr p j) = 0) ∧
    (aitchisonDistSq p q =
      (1 / (2 * (D : ℝ))) * (∑ a, ∑ b, (Real.log (p.val a / p.val b) - Real.log (q.val a / q.val b)) ^ 2)) ∧
    (clr (perturb p q) i = clr p i + clr q i) ∧
    ((1 / (D : ℝ)) * Real.log (1 / p.val k) - Real.log (D : ℝ) ≤ relativeEntropyJaynes p) ∧
    (∃ δ > 0, ∀ (p' : Simplex D) (k' : Fin D), p'.val k' < δ → M < relativeEntropyJaynes p') := by
  exact ⟨jaynes_clr_zero i,
         clr_trace_zero p,
         aitchison_pairwise_formula p q,
         clr_perturbation p q i,
         relative_entropy_facet_lower_bound p k,
         relative_entropy_diverges_at_facets M⟩

end InfoGeometry.Physics.AitchisonCLRSimplex
