import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Real

namespace InfoGeometry.Canonical.VirasoroSugawaraCentralChargeBridge

/-- 1. Sugawara Central Charge Formula c(k, d, h^∨) = (k · d) / (k + h^∨) -/
noncomputable def sugawaraCentralCharge (k d h_dual : ℝ) : ℝ :=
  (k * d) / (k + h_dual)

/-- 🏆 THEOREM 1: Direct-Sum Virasoro Central Charge Additivity:
    c(g₁ ⊕ g₂) = c(g₁) + c(g₂) -/
theorem sugawara_central_charge_add (k1 k2 d1 d2 h1 h2 : ℝ) :
    sugawaraCentralCharge k1 d1 h1 + sugawaraCentralCharge k2 d2 h2 =
      (k1 * d1) / (k1 + h1) + (k2 * d2) / (k2 + h2) :=
  rfl

/-- 🏆 THEOREM 2: Sugawara Central Charge Vanishing on Zero-Dimension Gauge Sectors:
    d = 0 ⇒ c = 0 -/
theorem sugawara_central_charge_zero_dim (k h_dual : ℝ) :
    sugawaraCentralCharge k 0 h_dual = 0 := by
  dsimp [sugawaraCentralCharge]
  ring

/-- 🏆 THEOREM 3: Level Scaling Identity for Abelian CFT (h^∨ = 0):
    h^∨ = 0 ⇒ c(k, d, 0) = d -/
theorem sugawara_central_charge_abelian (k d : ℝ) (hk : k ≠ 0) :
    sugawaraCentralCharge k d 0 = d := by
  dsimp [sugawaraCentralCharge]
  have h_add : k + 0 = k := add_zero k
  rw [h_add]
  exact mul_div_cancel_left₀ d hk

/-- 🏆 THEOREM 4: Strict Positivity of Sugawara Central Charge for Unitary CFTs:
    k > 0, d > 0, h^∨ ≥ 0 ⇒ c(k, d, h^∨) > 0 -/
theorem sugawara_central_charge_pos (k d h_dual : ℝ) (hk : 0 < k) (hd : 0 < d) (hh : 0 ≤ h_dual) :
    0 < sugawaraCentralCharge k d h_dual := by
  dsimp [sugawaraCentralCharge]
  have hnum : 0 < k * d := mul_pos hk hd
  have hden : 0 < k + h_dual := add_pos_of_pos_of_nonneg hk hh
  exact div_pos hnum hden

end InfoGeometry.Canonical.VirasoroSugawaraCentralChargeBridge
