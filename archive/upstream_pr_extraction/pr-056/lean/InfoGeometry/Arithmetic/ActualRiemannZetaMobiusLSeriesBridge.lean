import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The actual Riemann-zeta/Möbius `LSeries` bridge

This owner exposes the analytic identity already available in Mathlib on the
half-plane `1 < re s`.  It deliberately does not assert analytic continuation,
an identity on the critical strip, or any Riemann-hypothesis consequence.
-/

noncomputable section

open scoped LSeries.notation

namespace InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge

open ArithmeticFunction
open Complex

theorem mobius_LSeriesSummable_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (↗(moebius : ArithmeticFunction ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs

theorem actualRiemannZeta_mul_mobius_LSeries_eq_one
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * L ↗(moebius : ArithmeticFunction ℂ) s = 1 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs

theorem actualRiemannZeta_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_ne_zero_of_one_lt_re hs

theorem mobius_LSeries_eq_actualRiemannZeta_inv
    {s : ℂ} (hs : 1 < s.re) :
    L ↗(moebius : ArithmeticFunction ℂ) s = (riemannZeta s)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right
    (actualRiemannZeta_mul_mobius_LSeries_eq_one hs)

theorem one_div_actualRiemannZeta_eq_mobius_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    1 / riemannZeta s = L ↗(moebius : ArithmeticFunction ℂ) s := by
  simpa [one_div] using
    (mobius_LSeries_eq_actualRiemannZeta_inv hs).symm

theorem eq_mobius_LSeries_of_mul_eq_one
    {s : ℂ} (hs : 1 < s.re) (F : ℂ)
    (hF : riemannZeta s * F = 1) :
    F = L ↗(moebius : ArithmeticFunction ℂ) s := by
  calc
    F = (riemannZeta s)⁻¹ := eq_inv_of_mul_eq_one_right hF
    _ = L ↗(moebius : ArithmeticFunction ℂ) s :=
      (mobius_LSeries_eq_actualRiemannZeta_inv hs).symm

end InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge
