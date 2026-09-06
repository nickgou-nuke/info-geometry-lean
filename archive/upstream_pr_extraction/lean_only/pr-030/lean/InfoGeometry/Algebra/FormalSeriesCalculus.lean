import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Definitional formal-series calculus

This file records the algebraic lane where exponential and logarithmic symbols
are replaced by formal infinite series.

The carrier is `PowerSeries A`.  Its multiplication is coefficientwise Cauchy
product, so each coefficient calculation is a finite sum.  No analytic
completion, convergence theorem, norm, topology, or Taylor-remainder estimate is
used here.
-/

noncomputable section

namespace InfoGeometry.Algebra.FormalSeriesCalculus

variable (A : Type*) [CommRing A]

/-- Definitional geometric series `1 + X + X^2 + ...`. -/
def formalGeometric : PowerSeries A :=
  PowerSeries.mk fun _ => (1 : A)

@[simp]
theorem coeff_formalGeometric (n : ℕ) :
    PowerSeries.coeff n (formalGeometric A) = 1 := by
  simp [formalGeometric]

/-- The geometric series is the inverse of `1 - X`, coefficientwise. -/
theorem formalGeometric_mul_one_sub_X :
    formalGeometric A * (1 - PowerSeries.X) = 1 := by
  simpa [formalGeometric] using PowerSeries.mk_one_mul_one_sub_eq_one (S := A)

variable [Algebra ℚ A]

/-- Definitional exponential as the formal power series `∑ X^n / n!`. -/
abbrev formalExp : PowerSeries A :=
  PowerSeries.exp A

@[simp]
theorem coeff_formalExp (n : ℕ) :
    PowerSeries.coeff n (formalExp A) = algebraMap ℚ A (1 / (n.factorial : ℚ)) := by
  exact PowerSeries.coeff_exp n

@[simp]
theorem constantCoeff_formalExp :
    PowerSeries.constantCoeff (formalExp A) = 1 := by
  exact PowerSeries.constantCoeff_exp

/-- Definitional logarithm series for `log (1 + X)`. -/
def formalLogOnePlus : PowerSeries A :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / (n : ℚ))

@[simp]
theorem coeff_formalLogOnePlus (n : ℕ) :
    PowerSeries.coeff n (formalLogOnePlus A) =
      if n = 0 then 0 else algebraMap ℚ A (((-1 : ℚ) ^ (n + 1)) / (n : ℚ)) := by
  simp [formalLogOnePlus]

@[simp]
theorem constantCoeff_formalLogOnePlus :
    PowerSeries.constantCoeff (formalLogOnePlus A) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalLogOnePlus]
  simp

variable {A}
variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-- Algebra homomorphisms preserve the formal exponential series. -/
theorem map_formalExp (f : A →ₐ[ℚ] B) :
    PowerSeries.map f.toRingHom (formalExp A) = formalExp B := by
  exact PowerSeries.map_exp f.toRingHom

/-- Algebra homomorphisms preserve the definitional `log (1+X)` series. -/
theorem map_formalLogOnePlus (f : A →ₐ[ℚ] B) :
    PowerSeries.map f.toRingHom (formalLogOnePlus A) = formalLogOnePlus B := by
  ext n
  by_cases hn : n = 0
  · simp [formalLogOnePlus, hn]
  · simp [formalLogOnePlus, hn]

/-- Algebra homomorphisms preserve the geometric series. -/
theorem map_formalGeometric (f : A →ₐ[ℚ] B) :
    PowerSeries.map f.toRingHom (formalGeometric A) = formalGeometric B := by
  ext n
  simp [formalGeometric]

end InfoGeometry.Algebra.FormalSeriesCalculus
