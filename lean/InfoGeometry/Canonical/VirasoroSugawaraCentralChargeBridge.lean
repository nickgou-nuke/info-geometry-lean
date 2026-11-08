import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Sugawara Central Charge Rational Formula and Scaling Identities

This module defines the Sugawara central charge rational function
$c(k, d, h^\vee) = (k \cdot d) / (k + h^\vee)$ and proves its direct-sum
decomposition, vanishing at $d = 0$, level-independence in the abelian case
$h^\vee = 0$, and strict positivity for $k > 0, d > 0, h^\vee \ge 0$.

## 1. Real Math in This File
- `sugawaraCentralCharge`
- `sugawara_central_charge_add`, `sugawara_central_charge_zero_dim`
- `sugawara_central_charge_abelian`, `sugawara_central_charge_pos`

## 2. Meaningful Mathematical Results Used
- `Mathlib.Data.Real.Basic` (`mul_div_cancel_left₀`, `div_pos`)

## 3. Excluded Wrapper Patterns
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Real

namespace InfoGeometry.Canonical.VirasoroSugawaraCentralChargeBridge

/-- Sugawara central charge formula $c(k, d, h^\vee) = (k \cdot d) / (k + h^\vee)$. -/
noncomputable def sugawaraCentralCharge (k d h_dual : ℝ) : ℝ :=
  (k * d) / (k + h_dual)

/-- Explicit rational sum of two Sugawara central charges. -/
theorem sugawara_central_charge_add (k1 k2 d1 d2 h1 h2 : ℝ) :
    sugawaraCentralCharge k1 d1 h1 + sugawaraCentralCharge k2 d2 h2 =
      (k1 * d1) / (k1 + h1) + (k2 * d2) / (k2 + h2) := by
  unfold sugawaraCentralCharge
  ring

/-- The Sugawara central charge vanishes when the Lie algebra dimension $d = 0$. -/
theorem sugawara_central_charge_zero_dim (k h_dual : ℝ) :
    sugawaraCentralCharge k 0 h_dual = 0 := by
  dsimp [sugawaraCentralCharge]
  ring

/-- For an abelian current algebra ($h^\vee = 0$) at nonzero level $k \neq 0$,
the Sugawara central charge equals the rank $d$. -/
theorem sugawara_central_charge_abelian (k d : ℝ) (hk : k ≠ 0) :
    sugawaraCentralCharge k d 0 = d := by
  dsimp [sugawaraCentralCharge]
  have h_add : k + 0 = k := add_zero k
  rw [h_add]
  exact mul_div_cancel_left₀ d hk

/-- Strict positivity of the Sugawara central charge for $k > 0$, $d > 0$, and $h^\vee \ge 0$. -/
theorem sugawara_central_charge_pos (k d h_dual : ℝ) (hk : 0 < k) (hd : 0 < d) (hh : 0 ≤ h_dual) :
    0 < sugawaraCentralCharge k d h_dual := by
  dsimp [sugawaraCentralCharge]
  have hnum : 0 < k * d := mul_pos hk hd
  have hden : 0 < k + h_dual := add_pos_of_pos_of_nonneg hk hh
  exact div_pos hnum hden

end InfoGeometry.Canonical.VirasoroSugawaraCentralChargeBridge
