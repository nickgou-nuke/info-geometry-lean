import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Logarithms of homogeneous invariants

The analytic domain is `q x > 0`. Mathlib's real logarithm is total, so its
value at zero is not used as a boundary value. A degree-`d` invariant produces
a logarithmically homogeneous potential, not a degree-two cone potential.
-/

noncomputable section

namespace InfoGeometry.Analysis.LogHomogeneousPotential

def logPotential {E : Type*} (q : E → ℝ) (x : E) : ℝ := -Real.log (q x)

theorem logPotential_smul {E : Type*} [SMul ℝ E] (q : E → ℝ) (d : ℕ)
    (hq : ∀ r x, q (r • x) = r ^ d * q x)
    (x : E) (hx : 0 < q x) (r : ℝ) (hr : 0 < r) :
    logPotential q (r • x) = logPotential q x - d * Real.log r := by
  unfold logPotential
  rw [hq, Real.log_mul (ne_of_gt (pow_pos hr d)) (ne_of_gt hx), Real.log_pow]
  ring

theorem logPotential_zero_iff {E : Type*} (q : E → ℝ) (x : E) (hx : 0 < q x) :
    logPotential q x = 0 ↔ q x = 1 := by
  unfold logPotential
  rw [neg_eq_zero]
  constructor
  · exact Real.eq_one_of_pos_of_log_eq_zero hx
  · intro h
    rw [h, Real.log_one]

/-- The entropy readout is algebraic once the invariant is positive. -/
theorem sqrt_eq_exp_logPotential {E : Type*} (q : E → ℝ) (x : E) (hx : 0 < q x) :
    Real.sqrt (q x) = Real.exp (-logPotential q x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  simp [logPotential]
  ring

/-- Radial derivative in the scaling coordinate `r`. -/
theorem hasDerivAt_log_radial (c : ℝ) (hc : 0 < c) (d : ℕ) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => -Real.log (s ^ d * c)) (-(d : ℝ) / r) r := by
  convert (((hasDerivAt_pow d r).mul_const c).log
    (ne_of_gt (mul_pos (pow_pos hr d) hc))).neg using 1
  cases d with
  | zero => simp
  | succ d =>
    simp only [Nat.succ_sub_one, pow_succ]
    field_simp

theorem radial_second_derivative (d : ℕ) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => -(d : ℝ) / s) ((d : ℝ) / r ^ 2) r := by
  convert (hasDerivAt_inv (ne_of_gt hr)).const_mul (-(d : ℝ)) using 1
  simp [div_eq_mul_inv]

/-- A barrier sublevel bound gives a quantitative gap only when such a bound is supplied. -/
theorem sublevel_gap {E : Type*} (q : E → ℝ) (x : E) (hx : 0 < q x)
    (C : ℝ) (hC : logPotential q x ≤ C) : Real.exp (-C) ≤ q x := by
  have hlog : -C ≤ Real.log (q x) := by
    unfold logPotential at hC
    linarith
  simpa [Real.exp_log hx] using Real.exp_le_exp.mpr hlog

end InfoGeometry.Analysis.LogHomogeneousPotential
