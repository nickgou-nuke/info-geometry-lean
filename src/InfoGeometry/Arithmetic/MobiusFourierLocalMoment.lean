import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import InfoGeometry.Arithmetic.PrimeBitFiniteMobiusPolynomial

/-!
# Finite Möbius Fourier polynomials

This owner records the exact finite object used in Verjovsky's local-moment
criterion.  It proves only the algebraic normalization at the origin; no
asymptotic, moment bound, or Riemann-hypothesis equivalence is asserted.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open MeasureTheory

namespace InfoGeometry.Arithmetic.MobiusFourierLocalMoment

open InfoGeometry.Arithmetic.PrimeBitFiniteMobiusPolynomial
open InfoGeometry.Arithmetic.PrimeBitFiniteMertens
open InfoGeometry.Arithmetic.MobiusMertensRHEquivalence

def mobiusFourierPolynomial (N : ℕ) (t : ℝ) : ℂ :=
  (Real.rpow (N : ℝ) (-1 / 2) : ℂ) •
    primeCutoffMobiusPolynomial N
      (fun n => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)))

theorem mobiusFourierPolynomial_zero (N : ℕ) :
    mobiusFourierPolynomial N 0 =
    (Real.rpow (N : ℝ) (-1 / 2) : ℂ) • (mertensFunction N : ℂ) := by
  rw [mobiusFourierPolynomial]
  congr 1
  simpa [Complex.exp_zero] using
    (primeCutoffMobiusPolynomial_one_eq_mertensFunction N)

/-- The shrinking symmetric arc used for a finite local-moment readout. -/
def criticalArc (N : ℕ) (c : ℝ) : Set ℝ :=
  Set.Icc (-c / (N : ℝ)) (c / (N : ℝ))

/-- The unrooted normalized local `q`-moment of the Möbius polynomial. -/
def localMomentIntegral (N q : ℕ) (c : ℝ) : ℝ :=
  (N : ℝ) / (2 * c) *
    ∫ t in (-c / (N : ℝ))..(c / (N : ℝ)),
      ‖mobiusFourierPolynomial N t‖ ^ q

theorem continuous_mobiusFourierPolynomial (N : ℕ) :
    Continuous (mobiusFourierPolynomial N) := by
  classical
  unfold mobiusFourierPolynomial primeCutoffMobiusPolynomial
  fun_prop

theorem intervalIntegrable_localMoment_integrand (N q : ℕ) (c : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ‖mobiusFourierPolynomial N t‖ ^ q)
      volume (-c / (N : ℝ)) (c / (N : ℝ)) := by
  exact ((continuous_mobiusFourierPolynomial N).norm.pow q).intervalIntegrable _ _

@[simp] theorem criticalArc_length (N : ℕ) (c : ℝ) :
    c / (N : ℝ) - (-c / (N : ℝ)) = 2 * c / (N : ℝ) := by
  ring

end InfoGeometry.Arithmetic.MobiusFourierLocalMoment
