import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Cayley Jacobian Contraction at the Bost-Connes Boundary

W(β) = (β-½)/(β+½). At β→∞: W(β)→1 and the Jacobian 1/(β+½)²→0.

#### BUCKET 1: CLOSED FINITE THEOREMS
* `thermalCayley_eq_one_sub_inv`: algebraic identity
  `W(β) = 1 - 1/(β+½)` for `β ≠ -½`.
* `thermalCayley_jacobian_bound`: quadratic bound
  `1/(β+½)² ≤ 4/β²` for `β > ½`.
* `thermalCayley_jacobian_pos`: strict positivity
  `1/(β+½)² > 0` for `β > -½`.
* `thermalCayley_hasDerivAt`: exact derivative
  `dW/dβ = 1/(β+½)²` away from the pole.
* `thermalCayley_tendsto_one`: real-ray compactification limit `W(β) → 1`.
* `thermalCayley_jacobian_tendsto_zero`: Jacobian contraction limit
  `1/(β+½)² → 0`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
This file proves only the real-ray Cayley compactification and Jacobian
contraction.  It does not formalize a Cantor boundary, shattering map,
pushforward measure, or zero-temperature state-support theorem.
-/

set_option linter.unusedVariables false

open Filter
open Topology

noncomputable section

namespace InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions

noncomputable def thermalCayley (β : ℝ) : ℝ :=
  (β - (1 / 2 : ℝ)) / (β + (1 / 2 : ℝ))

/--
Algebraic identity: W(β) = 1 - 1/(β+½) for β ≠ -½.
-/
theorem thermalCayley_eq_one_sub_inv (β : ℝ) (hβ : β ≠ -1 / 2) :
    thermalCayley β = 1 - 1 / (β + (1 / 2 : ℝ)) := by
  dsimp [thermalCayley]
  have hden : β + (1 / 2 : ℝ) ≠ 0 := by
    intro h
    apply hβ
    linarith
  rw [show β - (1 / 2 : ℝ) = (β + (1 / 2 : ℝ)) - 1 by ring]
  rw [sub_div]
  rw [div_self hden]

/--
Quadratic Jacobian bound: for β > ½, 1/(β+½)² ≤ 4/β².
-/
theorem thermalCayley_jacobian_bound {β : ℝ} (hβ : β > 1 / 2) :
    1 / ((β + (1 / 2 : ℝ)) ^ 2) ≤ 4 / (β ^ 2) := by
  have hβpos : 0 < β := by linarith
  have hdenpos : 0 < β + (1 / 2 : ℝ) := by linarith
  have hβsq : 0 < β ^ 2 := pow_pos hβpos 2
  have hdensq : 0 < (β + (1 / 2 : ℝ)) ^ 2 := pow_pos hdenpos 2
  field_simp [hβsq.ne', hdensq.ne']
  nlinarith

/--
Strict positivity: for β > -½, 1/(β+½)² > 0.
-/
theorem thermalCayley_jacobian_pos {β : ℝ} (hβ : β > -1 / 2) :
    1 / ((β + (1 / 2 : ℝ)) ^ 2) > 0 := by
  have hdenpos : 0 < β + (1 / 2 : ℝ) := by linarith
  exact div_pos zero_lt_one (pow_pos hdenpos 2)

/--
Cayley boundary contraction — algebraic core.
-/
theorem cayley_boundary_contraction_core :
    (∀ β, β ≠ -1 / 2 → thermalCayley β = 1 - 1 / (β + (1 / 2 : ℝ))) ∧
      (∀ β, β > 1 / 2 → 1 / ((β + (1 / 2 : ℝ)) ^ 2) ≤ 4 / (β ^ 2)) ∧
        (∀ β, β > -1 / 2 → 1 / ((β + (1 / 2 : ℝ)) ^ 2) > 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact thermalCayley_eq_one_sub_inv
  · intro β hβ
    exact thermalCayley_jacobian_bound hβ
  · intro β hβ
    exact thermalCayley_jacobian_pos hβ

/--
Exact real derivative of the thermal Cayley transform.

`d/dβ ((β - 1/2) / (β + 1/2)) = 1 / (β + 1/2)^2`
-/
theorem thermalCayley_hasDerivAt (β : ℝ) (hβ : β ≠ -(1 / 2 : ℝ)) :
    HasDerivAt thermalCayley (1 / ((β + (1 / 2 : ℝ)) ^ 2)) β := by
  have h_num :
      HasDerivAt (fun x : ℝ => x - (1 / 2 : ℝ)) 1 β := by
    simpa using (hasDerivAt_id β).sub_const (1 / 2 : ℝ)
  have h_den :
      HasDerivAt (fun x : ℝ => x + (1 / 2 : ℝ)) 1 β := by
    simpa using (hasDerivAt_id β).add_const (1 / 2 : ℝ)
  have hden0 : β + (1 / 2 : ℝ) ≠ 0 := by
    intro hzero; apply hβ; linarith
  have hq := h_num.div h_den hden0
  unfold thermalCayley
  convert hq using 1
  field_simp [hden0]
  ring

private theorem tendsto_inv_beta_add_half :
    Tendsto (fun β : ℝ => 1 / (β + (1 / 2 : ℝ))) atTop (nhds 0) := by
  have h :=
    tendsto_mul_add_inv_atTop_nhds_zero (1 : ℝ) (1 / 2 : ℝ)
      (by norm_num : (1 : ℝ) ≠ 0)
  simpa [one_mul, one_div] using h

/--
Boundary convergence: W(β) → 1 as β → ∞.
-/
theorem thermalCayley_tendsto_one :
    Tendsto thermalCayley atTop (nhds 1) := by
  have h_inv := tendsto_inv_beta_add_half
  have h_ev_aux : thermalCayley =ᶠ[atTop] (fun β : ℝ => 1 - 1 / (β + (1 / 2 : ℝ))) := by
    filter_upwards [eventually_ne_atTop (-1 / 2 : ℝ)] with β hβ
    exact thermalCayley_eq_one_sub_inv β hβ
  have h_rhs :
    Tendsto
      (fun β : ℝ => 1 - 1 / (β + (1 / 2 : ℝ)))
      atTop
      (nhds 1) := by
    simpa using tendsto_const_nhds.sub h_inv
  exact h_rhs.congr' h_ev_aux.symm

/--
Quadratic Jacobian contraction: 1/(β+½)² → 0 as β → ∞.
-/
theorem thermalCayley_jacobian_tendsto_zero :
    Tendsto
      (fun β : ℝ => 1 / ((β + (1 / 2 : ℝ)) ^ 2))
      atTop
      (nhds 0) := by
  have h_inv :
      Tendsto
        (fun β : ℝ => (β + (1 / 2 : ℝ))⁻¹)
        atTop
        (nhds 0) := by
    simpa [one_div] using tendsto_inv_beta_add_half
  have h_sq := h_inv.pow 2
  simpa [one_div, inv_pow] using h_sq

/--
Full Cayley boundary contraction package.
-/
theorem cayley_boundary_contraction_limits :
    Tendsto thermalCayley atTop (nhds 1) ∧
    Tendsto
      (fun β : ℝ => 1 / ((β + (1 / 2 : ℝ)) ^ 2))
      atTop
      (nhds 0) :=
  ⟨thermalCayley_tendsto_one, thermalCayley_jacobian_tendsto_zero⟩

/-! ### 2. Complex Cayley Transform & Complex Jacobian -/

/-- The complex Cayley transform compactification map: $s \mapsto \frac{s - 1/2}{s + 1/2}$. -/
noncomputable def cayleyTransform (s : ℂ) : ℂ :=
  (s - (1 / 2 : ℂ)) / (s + (1 / 2 : ℂ))

/-- 🏆 THEOREM: Exact complex derivative of the Cayley transform. -/
theorem cayley_jacobian_derivative (s : ℂ) (h_safe : s ≠ -(1 / 2 : ℂ)) :
    HasDerivAt cayleyTransform (1 / (s + (1 / 2 : ℂ)) ^ 2) s := by
  have h1 : HasDerivAt (fun z : ℂ => z - (1 / 2 : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).sub_const (1 / 2 : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => z + (1 / 2 : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).add_const (1 / 2 : ℂ)
  have hden : s + (1 / 2 : ℂ) ≠ 0 := by
    intro h
    apply h_safe
    linear_combination h
  have hq := h1.div h2 hden
  unfold cayleyTransform
  convert hq using 1
  field_simp [hden]
  ring

/-- 🏆 THEOREM: The complex Jacobian norm vanishes quadratically at the boundary. -/
theorem cayley_jacobian_norm_vanishing :
    Tendsto (fun β : ℝ => ‖1 / ((β : ℂ) + (1 / 2 : ℂ)) ^ 2‖) atTop (nhds 0) := by
  have h_eq : (fun β : ℝ => ‖1 / ((β : ℂ) + (1 / 2 : ℂ)) ^ 2‖) =ᶠ[atTop]
      (fun β : ℝ => 1 / ((β + (1 / 2 : ℝ)) ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    have h_pos : 0 < β + (1 / 2 : ℝ) := by linarith
    have h_c_eq : ((β : ℂ) + (1 / 2 : ℂ)) = ((β + (1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [h_c_eq]
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg h_pos.le]
  exact thermalCayley_jacobian_tendsto_zero.congr' h_eq.symm

/-! ### 3. Dyadic Geometric Remainder Tail Extinction -/

/-- Dyadic geometric remainder tail on the Cantor branch: $R(\beta) = \frac{2^{-\beta}}{1 - 2^{-\beta}}$. -/
noncomputable def dyadicGeometricTail (β : ℝ) : ℝ :=
  (2 : ℝ) ^ (-β) / (1 - (2 : ℝ) ^ (-β))

/-- 🏆 THEOREM: Strict positivity of the geometric remainder tail for all $\beta > 0$. -/
theorem dyadicGeometricTail_pos (β : ℝ) (hβ : 0 < β) :
    0 < dyadicGeometricTail β := by
  unfold dyadicGeometricTail
  have h_base_pos : (0 : ℝ) < 2 := by norm_num
  have h_num : 0 < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos h_base_pos (-β)
  have h_lt_one : (2 : ℝ) ^ (-β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hβ)
  have h_den : 0 < 1 - (2 : ℝ) ^ (-β) := by linarith
  exact div_pos h_num h_den

/-- 🏆 THEOREM: The dyadic scale factor $2^{-\beta} \to 0$ as $\beta \to \infty$. -/
theorem tendsto_two_pow_neg_atTop :
    Tendsto (fun β : ℝ => (2 : ℝ) ^ (-β)) atTop (nhds 0) := by
  have h_log_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlinear : Tendsto (fun β : ℝ => Real.log 2 * β) atTop atTop :=
    Filter.Tendsto.const_mul_atTop h_log_pos Filter.tendsto_id
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
  have h_eq : (fun β : ℝ => (2 : ℝ) ^ (-β)) = (fun β : ℝ => Real.exp (- (Real.log 2 * β))) := by
    funext β
    rw [Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  rw [h_eq]
  simpa only [Function.comp_apply] using hexp

/-- 🏆 THEOREM: The dyadic geometric remainder tail vanishes at absolute zero ($\beta \to \infty$). -/
theorem dyadicGeometricTail_tendsto_zero :
    Tendsto dyadicGeometricTail atTop (nhds 0) := by
  unfold dyadicGeometricTail
  have h_num := tendsto_two_pow_neg_atTop
  have h_den : Tendsto (fun β : ℝ => 1 - (2 : ℝ) ^ (-β)) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h_num
  rw [sub_zero] at h_den
  have h_div := Tendsto.div h_num h_den (by norm_num : (1 : ℝ) ≠ 0)
  simpa [zero_div] using h_div

/-! ### 4. Master Grand Synthesis -/

/--
🏆 **MASTER SYNTHESIS: Souriau-Bost-Connes Boundary Extensions**

Unifies:
1. **Complex Cayley Jacobian**: $\frac{dW}{ds} = \frac{1}{(s + 1/2)^2}$.
2. **Jacobian Norm Vanishing**: $|\frac{dW}{ds}| \to 0$ as $\beta \to \infty$.
3. **Ray Compactification**: $W(\beta) \to 1$ as $\beta \to \infty$.
4. **Dyadic Remainder Positivity**: $R(\beta) > 0$ for $\beta > 0$.
5. **Absolute Zero Tail Extinction**: $R(\beta) \to 0$ as $\beta \to \infty$.
-/
theorem souriau_bost_connes_flow_extension_synthesis
    (β : ℝ) (hβ : 0 < β) (s : ℂ) (hs : s ≠ -(1 / 2 : ℂ)) :
    (HasDerivAt cayleyTransform (1 / (s + (1 / 2 : ℂ)) ^ 2) s) ∧
    (Tendsto (fun b : ℝ => ‖1 / ((b : ℂ) + (1 / 2 : ℂ)) ^ 2‖) atTop (nhds 0)) ∧
    (Tendsto thermalCayley atTop (nhds 1)) ∧
    (0 < dyadicGeometricTail β) ∧
    (Tendsto dyadicGeometricTail atTop (nhds 0)) :=
  ⟨cayley_jacobian_derivative s hs,
   cayley_jacobian_norm_vanishing,
   thermalCayley_tendsto_one,
   dyadicGeometricTail_pos β hβ,
   dyadicGeometricTail_tendsto_zero⟩

end InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
