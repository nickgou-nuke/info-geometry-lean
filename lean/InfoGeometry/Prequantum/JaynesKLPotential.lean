import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# InfoGeometry.Prequantum.JaynesKLPotential

Finite scalar Jaynes/KL information-potential facts.

The theorem `scalarKLDivergence_nonneg` proves the elementary positive-real
inequality

`0 ≤ x * log (x / y) - x + y`

for `x,y > 0`.  This is the scalar generalized-KL/Bregman shadow used by
finite Jaynes-style readouts.

This module is only the finite scalar positive-real KL/Bregman atom.  Broader
Araki, Souriau, Fenchel--Legendre, and reconstruction lanes are owned by their
corresponding repository modules and are not re-proved here.
-/

noncomputable section

namespace InfoGeometry.Prequantum.JaynesKLPotential

/-! ## Real lemma: Poisson / KL potential -/

/--
The scalar Poisson/KL potential is nonnegative:

`0 ≤ x - 1 - log x` for `0 < x`.

This is the scalar theorem behind the later operator lift
`Δ - I - log Δ ≥ 0`.
-/
theorem poissonPotential_nonneg
    (x : ℝ)
    (hx : 0 < x) :
    0 ≤ x - 1 - Real.log x := by
  have hlog : Real.log x ≤ x - 1 :=
    Real.log_le_sub_one_of_pos hx
  linarith

/-- The Poisson/KL potential vanishes at `1`. -/
@[simp] theorem poissonPotential_one :
    (1 : ℝ) - 1 - Real.log (1 : ℝ) = 0 := by
  simp

/-- Scalar generalized KL/Bregman potential on positive real weights. -/
def scalarKLDivergence (x y : ℝ) : ℝ :=
  x * Real.log (x / y) - x + y

/-- The scalar generalized KL/Bregman potential is nonnegative on positive weights. -/
theorem scalarKLDivergence_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ scalarKLDivergence x y := by
  have h_u : 0 < y / x := div_pos hy hx
  have h_log := Real.log_le_sub_one_of_pos h_u
  have h_log_div_yx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hy) (ne_of_gt hx)
  have h_log_div_xy : Real.log (x / y) = Real.log x - Real.log y :=
    Real.log_div (ne_of_gt hx) (ne_of_gt hy)
  have h_neg : Real.log (y / x) = - Real.log (x / y) := by
    rw [h_log_div_yx, h_log_div_xy]
    ring
  rw [h_neg] at h_log
  have h_mul := mul_le_mul_of_nonneg_left h_log (le_of_lt hx)
  have h_LHS : x * (- Real.log (x / y)) = - (x * Real.log (x / y)) := by ring
  have h_RHS : x * (y / x - 1) = y - x := by
    calc x * (y / x - 1) = x * (y / x) - x := by ring
         _ = y - x := by rw [mul_div_cancel₀ y (ne_of_gt hx)]
  rw [h_LHS, h_RHS] at h_mul
  unfold scalarKLDivergence
  linarith

/-- The scalar generalized KL/Bregman potential vanishes on the diagonal. -/
theorem scalarKLDivergence_self_zero (x : ℝ) (hx : 0 < x) :
    scalarKLDivergence x x = 0 := by
  unfold scalarKLDivergence
  rw [div_self (ne_of_gt hx), Real.log_one]
  ring

/-- Nonnegativity in the syntactic form of the pasted one-dimensional KL expression. -/
theorem kl_divergence_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ x * Real.log (x / y) - x + y :=
  scalarKLDivergence_nonneg x y hx hy

/-- Diagonal vanishing in the syntactic form of the pasted one-dimensional KL expression. -/
theorem kl_divergence_self_zero (x : ℝ) (hx : 0 < x) :
    x * Real.log (x / x) - x + x = 0 :=
  scalarKLDivergence_self_zero x hx

end InfoGeometry.Prequantum.JaynesKLPotential
