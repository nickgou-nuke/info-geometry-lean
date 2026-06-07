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

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
The limit theorems `W(β) → 1` and `1/(β+½)² → 0` at `atTop` are intentionally
not claimed here; this file records only the algebraic contraction core.
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
  have hsum : (β - (1 / 2 : ℝ)) / (β + (1 / 2 : ℝ)) + 1 / (β + (1 / 2 : ℝ)) = 1 := by
    rw [← add_div]
    have : β - (1 / 2 : ℝ) + 1 = β + (1 / 2 : ℝ) := by ring
    rw [this]
    exact div_self hden
  linarith

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

end InfoGeometry.Dynamics.SouriauBostConnesFlowExtensions
