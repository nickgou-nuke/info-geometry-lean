import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.PrimeLocalFugacityOrder

/--
Real modulus model for local fugacity:

`|exp (-(s - 1/2) ell)| = exp (-(Re(s)-1/2) ell)`.
-/
def localFugacityAbsModel (fieldRe ell : ℝ) : ℝ :=
  Real.exp (-(fieldRe * ell))

theorem localFugacityAbs_lt_one
    {fieldRe ell : ℝ}
    (hfield : 0 < fieldRe)
    (hell : 0 < ell) :
    localFugacityAbsModel fieldRe ell < 1 := by
  unfold localFugacityAbsModel
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

theorem one_lt_localFugacityAbs
    {fieldRe ell : ℝ}
    (hfield : fieldRe < 0)
    (hell : 0 < ell) :
    1 < localFugacityAbsModel fieldRe ell := by
  unfold localFugacityAbsModel
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith)

end InfoGeometry.Canonical.PrimeLocalFugacityOrder
