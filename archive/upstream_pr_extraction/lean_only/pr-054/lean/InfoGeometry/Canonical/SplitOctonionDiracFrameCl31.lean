import Mathlib
import InfoGeometry.Canonical.ZornSpinor

/-!
# A real `Cl(3,1)` frame in the canonical Zorn carrier

The four displayed generators are native Zorn elements.  This owner proves
only their finite multiplication table: one generator squares to `-1`, the
other three square to `+1`, and distinct generators anticommute.  It does not
claim that the nonassociative Zorn carrier is an associative Clifford algebra.
-/

namespace InfoGeometry.Canonical.SplitOctonionDiracFrameCl31

noncomputable section

open InfoGeometry.Canonical.ZornMatrix

def gamma0 : ZornMatrix ℝ := chiralLowerBasis 2 - chiralUpperBasis 2

def gamma1 : ZornMatrix ℝ := chiralUpperBasis 1 + chiralLowerBasis 1

def gamma2 : ZornMatrix ℝ := -(chiralUpperBasis 0 + chiralLowerBasis 0)

def gamma3 : ZornMatrix ℝ := -(zornPlus - zornMinus)

def anticommutator (x y : ZornMatrix ℝ) : ZornMatrix ℝ := x * y + y * x

private theorem fin_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem fin_one_ne_two : (1 : Fin 3) ≠ 2 := by decide
private theorem fin_two_eq_two : (2 : Fin 3) = 2 := rfl

theorem gamma0_sq : gamma0 * gamma0 = -(1 : ZornMatrix ℝ) := by
  rw [show (1 : ZornMatrix ℝ) = { a := 1, b := 1, x := 0, y := 0 } by rfl,
    ZornMatrix.neg_def]
  apply ZornMatrix.ext
  · simp [gamma0, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_eq_add_neg, ZornMatrix.neg_def, fin_zero_ne_two,
      fin_one_ne_two]
  · simp [gamma0, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_eq_add_neg, ZornMatrix.neg_def, fin_zero_ne_two,
      fin_one_ne_two]
  · funext i
    fin_cases i <;> simp [gamma0, chiralLowerBasis, chiralUpperBasis,
      mul_def, mul, dot, cross, sub_eq_add_neg, ZornMatrix.neg_def,
      fin_zero_ne_two, fin_one_ne_two]
  · funext i
    fin_cases i <;> simp [gamma0, chiralLowerBasis, chiralUpperBasis,
      mul_def, mul, dot, cross, sub_eq_add_neg, ZornMatrix.neg_def,
      fin_zero_ne_two, fin_one_ne_two]

theorem gamma1_sq : gamma1 * gamma1 = (1 : ZornMatrix ℝ) := by
  change gamma1 * gamma1 = { a := 1, b := 1, x := 0, y := 0 }
  apply ZornMatrix.ext <;>
    simp [gamma1, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_eq_add_neg, add_comm]

theorem gamma2_sq : gamma2 * gamma2 = (1 : ZornMatrix ℝ) := by
  change gamma2 * gamma2 = { a := 1, b := 1, x := 0, y := 0 }
  apply ZornMatrix.ext <;>
    simp [gamma2, chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
      sub_eq_add_neg, add_comm]

theorem gamma3_sq : gamma3 * gamma3 = (1 : ZornMatrix ℝ) := by
  change gamma3 * gamma3 = { a := 1, b := 1, x := 0, y := 0 }
  apply ZornMatrix.ext <;>
    simp [gamma3, zornPlus, zornMinus, mul_def, mul, dot, cross,
      sub_eq_add_neg, add_comm]

theorem gamma0_gamma1_anticommute : anticommutator gamma0 gamma1 = 0 := by
  change anticommutator gamma0 gamma1 = { a := 0, b := 0, x := 0, y := 0 }
  apply ZornMatrix.ext <;> simp [anticommutator, gamma0, gamma1,
    chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
    sub_eq_add_neg]

theorem gamma0_gamma2_anticommute : anticommutator gamma0 gamma2 = 0 := by
  change anticommutator gamma0 gamma2 = { a := 0, b := 0, x := 0, y := 0 }
  apply ZornMatrix.ext <;> simp [anticommutator, gamma0, gamma2,
    chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
    sub_eq_add_neg]

theorem gamma0_gamma3_anticommute : anticommutator gamma0 gamma3 = 0 := by
  change anticommutator gamma0 gamma3 = { a := 0, b := 0, x := 0, y := 0 }
  apply ZornMatrix.ext <;> simp [anticommutator, gamma0, gamma3,
    chiralLowerBasis, chiralUpperBasis, zornPlus, zornMinus, mul_def, mul,
    dot, cross, sub_eq_add_neg]

theorem gamma1_gamma2_anticommute : anticommutator gamma1 gamma2 = 0 := by
  change anticommutator gamma1 gamma2 = { a := 0, b := 0, x := 0, y := 0 }
  apply ZornMatrix.ext <;> simp [anticommutator, gamma1, gamma2,
    chiralLowerBasis, chiralUpperBasis, mul_def, mul, dot, cross,
    sub_eq_add_neg]

theorem gamma1_gamma3_anticommute : anticommutator gamma1 gamma3 = 0 := by
  change anticommutator gamma1 gamma3 = { a := 0, b := 0, x := 0, y := 0 }
  apply ZornMatrix.ext <;> simp [anticommutator, gamma1, gamma3,
    chiralLowerBasis, chiralUpperBasis, zornPlus, zornMinus, mul_def, mul,
    dot, cross, sub_eq_add_neg]

theorem gamma2_gamma3_anticommute : anticommutator gamma2 gamma3 = 0 := by
  change anticommutator gamma2 gamma3 = { a := 0, b := 0, x := 0, y := 0 }
  apply ZornMatrix.ext <;> simp [anticommutator, gamma2, gamma3,
    chiralLowerBasis, chiralUpperBasis, zornPlus, zornMinus, mul_def, mul,
    dot, cross, sub_eq_add_neg]

end
end InfoGeometry.Canonical.SplitOctonionDiracFrameCl31
