import Mathlib

/-!
# InfoGeometry.Canonical.FenchelExpLogCore

Concrete Fenchel core facts for `f(x)=exp x` on `ℝ`.

For `y>0`, define `φ_y(x) = y*x - exp x`.
This file proves:
1. `x = log y` is stationary.
2. `φ_y(log y) = y*log y - y`.
3. Global upper bound `φ_y(x) ≤ y*log y - y`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.FenchelExpLogCore

open Real

noncomputable section

def phi (y x : ℝ) : ℝ := y * x - Real.exp x

theorem phi_hasDerivAt (y x : ℝ) :
    HasDerivAt (phi y) (y - Real.exp x) x := by
  unfold phi
  simpa using (hasDerivAt_const x y).mul (hasDerivAt_id x) |>.sub (Real.hasDerivAt_exp x)

theorem phi_stationary_at_log (y : ℝ) (hy : 0 < y) :
    HasDerivAt (phi y) 0 (Real.log y) := by
  have hder := phi_hasDerivAt y (Real.log y)
  have hyexp : Real.exp (Real.log y) = y := Real.exp_log hy
  simpa [hyexp] using hder

theorem phi_at_log (y : ℝ) (hy : 0 < y) :
    phi y (Real.log y) = y * Real.log y - y := by
  unfold phi
  rw [Real.exp_log hy]

theorem phi_le_fenchelValue (y x : ℝ) (hy : 0 < y) :
    phi y x ≤ y * Real.log y - y := by
  have hexp : Real.exp (x - Real.log y) ≥ (x - Real.log y) + 1 := by
    exact Real.add_one_le_exp (x - Real.log y)
  have hy' : 0 ≤ y := le_of_lt hy
  have hmul := mul_le_mul_of_nonneg_left hexp hy'
  have hexp_split : Real.exp x = y * Real.exp (x - Real.log y) := by
    rw [show x = (x - Real.log y) + Real.log y by ring]
    rw [Real.exp_add, Real.exp_log hy]
    ring
  unfold phi
  rw [hexp_split]
  have hstep : y * ((x - Real.log y) + 1) = y * x - (y * Real.log y - y) := by ring
  linarith

theorem phi_log_is_global_maximizer (y x : ℝ) (hy : 0 < y) :
    phi y x ≤ phi y (Real.log y) := by
  calc
    phi y x ≤ y * Real.log y - y := phi_le_fenchelValue y x hy
    _ = phi y (Real.log y) := (phi_at_log y hy).symm

end

end InfoGeometry.Canonical.FenchelExpLogCore
