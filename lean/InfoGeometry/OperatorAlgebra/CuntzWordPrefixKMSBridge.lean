import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

set_option linter.unusedSimpArgs false

/-!
# Cuntz Word Prefix Modular Readout Bridge

This module establishes exact finite scalar modular readout identities for
word-indexed gauge coefficients.  The displayed cases are compatible with the
Cuntz prefix calculus, but this owner does not itself define multiplication,
the star algebra, a Cuntz quotient, or the full KMS condition on arbitrary
word monomials:

1. **Modular Factor:**
   $$\Delta(u, v) = 2^{-(|u| - |v|)} = (1/2)^{|u| - |v|}$$

2. **Equal Inner Words ($v = x$):**
   $$\varphi_0(S_u S_u^*) = \Delta(u, v) \varphi_0(S_v S_v^*)$$

3. **Right Prefix ($x = v ++ w$):**
   $$\varphi_0(S_{u ++ w} S_{u ++ w}^*) = \Delta(u, v) \varphi_0(S_{v ++ w} S_{v ++ w}^*)$$

4. **Left Prefix ($v = x ++ w$):**
   $$\varphi_0(S_{y ++ w} S_{y ++ w}^*) = \Delta(y ++ w, x ++ w) \varphi_0(S_{x ++ w} S_{x ++ w}^*)$$

5. **Cocycle / Groupoid Laws:**
   $$\Delta(u, v) \Delta(v, w) = \Delta(u, w), \qquad \Delta(u, v) \Delta(v, u) = 1.$$
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CuntzWordPrefixKMSBridge

open Complex
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

abbrev Word := List Bool

theorem half_ne_zero : (1 / 2 : ℂ) ≠ 0 := by norm_num

/-- The modular factor $2^{-(|u|-|v|)}$ associated to the word monomial $S_u S_v^*$. -/
def modularFactor (u v : Word) : ℂ :=
  (1 / 2 : ℂ) ^ ((u.length : ℤ) - (v.length : ℤ))

/-- 🏆 THEOREM 1: Equal inner words $v = x$.
    $\varphi_0(S_u S_u^*) = 2^{-(|u|-|v|)} \varphi_0(S_v S_v^*)$. -/
theorem kms_case_equal_matched (u v : Word) :
    canonicalGaugeState u u =
      modularFactor u v * canonicalGaugeState v v := by
  have h1 : canonicalGaugeState u u = (1 / 2 : ℂ) ^ (u.length : ℤ) := by
    rw [canonicalGaugeState_proj]
    exact (zpow_natCast (1 / 2 : ℂ) u.length).symm
  have h2 : canonicalGaugeState v v = (1 / 2 : ℂ) ^ (v.length : ℤ) := by
    rw [canonicalGaugeState_proj]
    exact (zpow_natCast (1 / 2 : ℂ) v.length).symm
  dsimp [modularFactor]
  rw [h1, h2, ← zpow_add₀ half_ne_zero]
  congr 1
  ring

/-- 🏆 THEOREM 2: Equal inner words with unmatched outer sector $y \neq u$. -/
theorem kms_case_equal_unmatched (u v y : Word) (h : u ≠ y) :
    canonicalGaugeState u y = 0 ∧
    (if y = u then canonicalGaugeState v v else (0 : ℂ)) = 0 := by
  constructor
  · exact canonicalGaugeState_cross h
  · rw [if_neg (ne_comm.mp h)]

/-- 🏆 THEOREM 3: Right prefix $x = v ++ w$ with matched outer sector $y = u ++ w$.
    $\varphi_0(S_{u ++ w} S_{u ++ w}^*) = 2^{-(|u|-|v|)} \varphi_0(S_{v ++ w} S_{v ++ w}^*)$. -/
theorem kms_case_right_prefix_matched (u v w : Word) :
    canonicalGaugeState (u ++ w) (u ++ w) =
      modularFactor u v * canonicalGaugeState (v ++ w) (v ++ w) := by
  have h1 : canonicalGaugeState (u ++ w) (u ++ w) = (1 / 2 : ℂ) ^ ((u ++ w).length : ℤ) := by
    rw [canonicalGaugeState_proj]
    exact (zpow_natCast (1 / 2 : ℂ) (u ++ w).length).symm
  have h2 : canonicalGaugeState (v ++ w) (v ++ w) = (1 / 2 : ℂ) ^ ((v ++ w).length : ℤ) := by
    rw [canonicalGaugeState_proj]
    exact (zpow_natCast (1 / 2 : ℂ) (v ++ w).length).symm
  dsimp [modularFactor]
  rw [h1, h2, List.length_append, List.length_append]
  push_cast
  rw [← zpow_add₀ half_ne_zero]
  congr 1
  ring

/-- 🏆 THEOREM 4: Left prefix $v = x ++ w$ with matched outer sector $u = y ++ w$.
    $\varphi_0(S_{y ++ w} S_{y ++ w}^*) = 2^{-(|y ++ w|-|x ++ w|)} \varphi_0(S_{x ++ w} S_{x ++ w}^*)$. -/
theorem kms_case_left_prefix_matched (x y w : Word) :
    canonicalGaugeState (y ++ w) (y ++ w) =
      modularFactor (y ++ w) (x ++ w) * canonicalGaugeState (x ++ w) (x ++ w) := by
  have h1 : canonicalGaugeState (y ++ w) (y ++ w) = (1 / 2 : ℂ) ^ ((y ++ w).length : ℤ) := by
    rw [canonicalGaugeState_proj]
    exact (zpow_natCast (1 / 2 : ℂ) (y ++ w).length).symm
  have h2 : canonicalGaugeState (x ++ w) (x ++ w) = (1 / 2 : ℂ) ^ ((x ++ w).length : ℤ) := by
    rw [canonicalGaugeState_proj]
    exact (zpow_natCast (1 / 2 : ℂ) (x ++ w).length).symm
  dsimp [modularFactor]
  rw [h1, h2, List.length_append, List.length_append]
  push_cast
  rw [← zpow_add₀ half_ne_zero]
  congr 1
  ring

/-- 🏆 THEOREM 5: Modular factor groupoid/cocycle law:
    $\Delta(u, v) \Delta(v, w) = \Delta(u, w)$. -/
theorem modularFactor_trans (u v w : Word) :
    modularFactor u v * modularFactor v w = modularFactor u w := by
  dsimp [modularFactor]
  rw [← zpow_add₀ half_ne_zero]
  congr 1
  ring

/-- 🏆 THEOREM 6: Modular factor inversion law:
    $\Delta(u, v) \Delta(v, u) = 1$. -/
theorem modularFactor_inv (u v : Word) :
    modularFactor u v * modularFactor v u = 1 := by
  dsimp [modularFactor]
  rw [← zpow_add₀ half_ne_zero]
  have : (u.length : ℤ) - v.length + ((v.length : ℤ) - u.length) = 0 := by ring
  rw [this, zpow_zero]

end InfoGeometry.OperatorAlgebra.CuntzWordPrefixKMSBridge
