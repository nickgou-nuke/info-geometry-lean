import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.RindlerWeylDecomposition

Mathematical Proof:
This file formally proves the Rindler-Weyl coordinate decomposition of the
diagonal Zorn cell (the 1+1D lightcone).

Given the positive diagonal coordinates `r > 0` and `s > 0` of the Zorn cell,
the Weyl dilaton scale `ξ` and the Rindler boost rapidity `η` are defined
as the symmetric and antisymmetric logarithmic combinations:
* `ξ = (ln(r) + ln(s)) / 2`  (The Dilaton / Massieu Potential)
* `η = (ln(r) - ln(s)) / 2`  (The Rindler Rapidity / Modular Parameter)

We prove that `r` and `s` are reconstructed exactly via the exponential map:
* `r = exp(ξ + η)`
* `s = exp(ξ - η)`

No placeholders. No `sorry`.
-/

namespace InfoGeometry.Canonical.RindlerWeylDecomposition

noncomputable section

variable (r s : Real)

/-- Logarithmic geometric-mean coordinate on the positive diagonal sector. -/
def xi : Real :=
  (Real.log r + Real.log s) / 2

/-- Half-logarithmic ratio coordinate. -/
def eta : Real :=
  (Real.log r - Real.log s) / 2

/--
The Rindler-Weyl reconstruction theorem for the left-moving coordinate `r`.
`r = exp(ξ + η)`.
-/
theorem r_eq_exp_xi_add_eta :
    (hr : 0 < r) → Real.exp (xi r s + eta r s) = r := by
  intro hr
  unfold xi eta
  have h_add : (Real.log r + Real.log s) / 2 + (Real.log r - Real.log s) / 2 = Real.log r := by
    ring
  rw [h_add]
  exact Real.exp_log hr

/--
The Rindler-Weyl reconstruction theorem for the right-moving coordinate `s`.
`s = exp(ξ - η)`.
-/
theorem s_eq_exp_xi_sub_eta :
    (hs : 0 < s) → Real.exp (xi r s - eta r s) = s := by
  intro hs
  unfold xi eta
  have h_sub : (Real.log r + Real.log s) / 2 - (Real.log r - Real.log s) / 2 = Real.log s := by
    ring
  rw [h_sub]
  exact Real.exp_log hs

/-- Symmetric/antisymmetric decomposition recovers `log r`. -/
theorem xi_add_eta_eq_log_r :
    xi r s + eta r s = Real.log r := by
  unfold xi eta
  ring

/-- Symmetric/antisymmetric decomposition recovers `log s`. -/
theorem xi_sub_eta_eq_log_s :
    xi r s - eta r s = Real.log s := by
  unfold xi eta
  ring

/-- Exponential corollary: `exp (xi + eta) = r` under `r > 0`. -/
theorem exp_xi_add_eta_eq_r (hr : 0 < r) :
    Real.exp (xi r s + eta r s) = r := by
  rw [xi_add_eta_eq_log_r (r := r) (s := s)]
  exact Real.exp_log hr

/-- Exponential corollary: `exp (xi - eta) = s` under `s > 0`. -/
theorem exp_xi_sub_eta_eq_s (hs : 0 < s) :
    Real.exp (xi r s - eta r s) = s := by
  rw [xi_sub_eta_eq_log_s (r := r) (s := s)]
  exact Real.exp_log hs

/-- Inverse log identity for `r`. -/
theorem log_r_eq_xi_add_eta :
    Real.log r = xi r s + eta r s := by
  simpa using (xi_add_eta_eq_log_r (r := r) (s := s)).symm

/-- Inverse log identity for `s`. -/
theorem log_s_eq_xi_sub_eta :
    Real.log s = xi r s - eta r s := by
  simpa using (xi_sub_eta_eq_log_s (r := r) (s := s)).symm

/-- Multiplicative reconstruction: `exp (2*xi) = r*s` for positive `r,s`. -/
theorem exp_two_mul_xi_eq_mul (hr : 0 < r) (hs : 0 < s) :
    Real.exp (2 * xi r s) = r * s := by
  unfold xi
  have hlin : (2 : Real) * ((Real.log r + Real.log s) / 2) = Real.log r + Real.log s := by
    ring
  rw [hlin, Real.exp_add, Real.exp_log hr, Real.exp_log hs]

/-- Quotient reconstruction: `exp (2*eta) = r / s` for positive `r,s`. -/
theorem exp_two_mul_eta_eq_div (hr : 0 < r) (hs : 0 < s) :
    Real.exp (2 * eta r s) = r / s := by
  unfold eta
  have hlin : (2 : Real) * ((Real.log r - Real.log s) / 2) = Real.log r - Real.log s := by
    ring
  rw [hlin, sub_eq_add_neg, Real.exp_add, Real.exp_log hr, Real.exp_neg, Real.exp_log hs]
  field_simp [hs.ne']

end

end InfoGeometry.Canonical.RindlerWeylDecomposition
