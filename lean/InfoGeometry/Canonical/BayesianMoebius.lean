import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical

noncomputable def logit (p : ℝ) : ℝ := Real.log (p / (1 - p))

noncomputable def bayesUpdate (Λ p : ℝ) : ℝ := (Λ * p) / (1 + (Λ - 1) * p)

theorem logit_bayesUpdate (Λ p : ℝ) (hp1 : 0 < p) (hp2 : p < 1) (hΛ : 0 < Λ) :
    logit (bayesUpdate Λ p) = logit p + Real.log Λ := by
  dsimp [logit, bayesUpdate]
  let D := 1 + (Λ - 1) * p
  have hD : 0 < D := by
    dsimp [D]
    have h_rew : 1 + (Λ - 1) * p = (1 - p) + Λ * p := by ring
    rw [h_rew]
    exact add_pos (sub_pos.mpr hp2) (mul_pos hΛ hp1)
  have hD_ne : D ≠ 0 := ne_of_gt hD
  
  have h_arg_rewrite : ((Λ * p) / D) / (1 - (Λ * p) / D) = (Λ * p) / (1 - p) := by
    have h_sub : 1 - (Λ * p) / D = (D - Λ * p) / D := by 
      have h1 : (1 : ℝ) = D / D := (div_self hD_ne).symm
      nth_rw 1 [h1]
      exact (sub_div D (Λ * p) D).symm
    have h_num : D - Λ * p = 1 - p := by dsimp [D]; ring
    rw [h_sub, h_num]
    have h_num_mul : (Λ * p) / D = (Λ * p) * (1 / D) := div_eq_mul_one_div (Λ * p) D
    have h_den_mul : (1 - p) / D = (1 - p) * (1 / D) := div_eq_mul_one_div (1 - p) D
    rw [h_num_mul, h_den_mul]
    have h_div_div : ((Λ * p) * (1 / D)) / ((1 - p) * (1 / D)) = (Λ * p) / (1 - p) := by
      exact mul_div_mul_right (Λ * p) (1 - p) (one_div_ne_zero hD_ne)
    exact h_div_div

  rw [h_arg_rewrite]
  have h_div_mul : (Λ * p) / (1 - p) = Λ * (p / (1 - p)) := by ring
  rw [h_div_mul]
  have h_p_sub_pos : 0 < p / (1 - p) := div_pos hp1 (sub_pos.mpr hp2)
  rw [Real.log_mul (ne_of_gt hΛ) (ne_of_gt h_p_sub_pos)]
  ring

noncomputable def naturalCoordinate (a b X B : ℝ) : ℝ := (1 / a) * Real.log ((a * X + b) / (a * B + b))

theorem naturalCoordinate_eq_logit (a b X B : ℝ) (ha : 0 < a) 
    (hX : 0 < a * X + b) (hB : 0 < a * B + b) :
    naturalCoordinate a b X B = (1 / a) * logit ((a * X + b) / (a * X + a * B + 2 * b)) := by
  dsimp [naturalCoordinate, logit]
  let num := a * X + b
  let den := a * B + b
  have h_sum_pos : 0 < num + den := add_pos hX hB
  have h_sum_ne : num + den ≠ 0 := ne_of_gt h_sum_pos
  
  have h_equiv : (num / (num + den)) / (1 - num / (num + den)) = num / den := by
    have h_sub : 1 - num / (num + den) = ((num + den) - num) / (num + den) := by
      have h1 : (1 : ℝ) = (num + den) / (num + den) := (div_self h_sum_ne).symm
      nth_rw 1 [h1]
      exact (sub_div (num + den) num (num + den)).symm
    have h_num_sub : (num + den) - num = den := by ring
    rw [h_sub, h_num_sub]
    have h_num_mul : num / (num + den) = num * (1 / (num + den)) := div_eq_mul_one_div num (num + den)
    have h_den_mul : den / (num + den) = den * (1 / (num + den)) := div_eq_mul_one_div den (num + den)
    rw [h_num_mul, h_den_mul]
    exact mul_div_mul_right num den (one_div_ne_zero h_sum_ne)
  have h_den : a * X + a * B + 2 * b = num + den := by dsimp [num, den]; ring
  rw [h_den, h_equiv]

noncomputable def updateSum (ρ S r X : ℝ) : ℝ := ρ * S + r * X
noncomputable def updateMass (ρ N r : ℝ) : ℝ := ρ * N + r
noncomputable def updateBackground (S N : ℝ) : ℝ := S / N

theorem barycentric_update (ρ S N r X : ℝ) (hN : 0 < N) (hr : 0 ≤ r) (hρ : 0 < ρ) (h_mass : 0 < ρ * N + r) :
    updateBackground (updateSum ρ S r X) (updateMass ρ N r) = 
    updateBackground S N + (r / (ρ * N + r)) * (X - updateBackground S N) := by
  dsimp [updateBackground, updateSum, updateMass]
  have hN_ne : N ≠ 0 := ne_of_gt hN
  have hM_ne : ρ * N + r ≠ 0 := ne_of_gt h_mass
  
  have h_rhs : S / N + (r / (ρ * N + r)) * (X - S / N) = (ρ * S + r * X) / (ρ * N + r) := by
    have hX : X - S / N = (X * N - S) / N := by
      have h1 : X = (X * N) / N := (mul_div_cancel_right₀ X hN_ne).symm
      nth_rw 1 [h1]
      exact (sub_div (X * N) S N).symm
    rw [hX]
    have h_mul : (r / (ρ * N + r)) * ((X * N - S) / N) = (r * (X * N - S)) / ((ρ * N + r) * N) := div_mul_div_comm r (ρ * N + r) (X * N - S) N
    rw [h_mul]
    have h_denom : (ρ * N + r) * N = N * (ρ * N + r) := mul_comm (ρ * N + r) N
    rw [h_denom]
    have h_add : S / N + (r * (X * N - S)) / (N * (ρ * N + r)) = (S * (ρ * N + r) + r * (X * N - S)) / (N * (ρ * N + r)) := by
      have h_add_div : (S * (ρ * N + r)) / (N * (ρ * N + r)) + (r * (X * N - S)) / (N * (ρ * N + r)) = (S * (ρ * N + r) + r * (X * N - S)) / (N * (ρ * N + r)) := (add_div (S * (ρ * N + r)) (r * (X * N - S)) (N * (ρ * N + r))).symm
      have h_cancel : (S * (ρ * N + r)) / (N * (ρ * N + r)) = S / N := by
        exact mul_div_mul_right S N hM_ne
      rw [← h_cancel]
      exact h_add_div
    rw [h_add]
    have h_num : S * (ρ * N + r) + r * (X * N - S) = N * (ρ * S + r * X) := by ring
    rw [h_num]
    have h_denom2 : N * (ρ * N + r) = (ρ * N + r) * N := mul_comm N (ρ * N + r)
    rw [h_denom2]
    have h_res : (N * (ρ * S + r * X)) / ((ρ * N + r) * N) = (ρ * S + r * X) / (ρ * N + r) := by
      rw [mul_comm N (ρ * S + r * X)]
      exact mul_div_mul_right (ρ * S + r * X) (ρ * N + r) hN_ne
    exact h_res
  rw [h_rhs]

noncomputable def evidenceGapEncode (N_O ε : ℝ) : ℝ := 1 / (1 + Real.exp (-(N_O / ε)))

theorem splitNorm_encode_logit (N_O ε : ℝ) (hε : 0 < ε) :
    N_O = ε * logit (evidenceGapEncode N_O ε) := by
  dsimp [evidenceGapEncode, logit]
  let E := Real.exp (-(N_O / ε))
  have hE_pos : 0 < E := Real.exp_pos (-(N_O / ε))
  have h_add_ne : 1 + E ≠ 0 := ne_of_gt (by linarith)
  
  have h_equiv : (1 / (1 + E)) / (1 - 1 / (1 + E)) = 1 / E := by
    have h_sub : 1 - 1 / (1 + E) = ((1 + E) - 1) / (1 + E) := by
      have h1 : (1 : ℝ) = (1 + E) / (1 + E) := (div_self h_add_ne).symm
      nth_rw 1 [h1]
      exact (sub_div (1 + E) 1 (1 + E)).symm
    have h_num : (1 + E) - 1 = E := by ring
    rw [h_sub, h_num]
    have h_num_mul : 1 / (1 + E) = 1 * (1 / (1 + E)) := by ring
    have h_den_mul : E / (1 + E) = E * (1 / (1 + E)) := div_eq_mul_one_div E (1 + E)
    rw [h_num_mul, h_den_mul]
    exact mul_div_mul_right 1 E (one_div_ne_zero h_add_ne)
    
  rw [h_equiv]
  have h_inv : 1 / E = Real.exp (N_O / ε) := by
    dsimp [E]
    rw [one_div, ← Real.exp_neg, neg_neg]
  rw [h_inv, Real.log_exp (N_O / ε)]
  exact (mul_div_cancel₀ N_O (ne_of_gt hε)).symm

end InfoGeometry.Canonical
