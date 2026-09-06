import Mathlib

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
  exact ⟨thermalCayley_eq_one_sub_inv,
    fun β hβ => thermalCayley_jacobian_bound hβ,
    fun β hβ => thermalCayley_jacobian_pos hβ⟩

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

end InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
