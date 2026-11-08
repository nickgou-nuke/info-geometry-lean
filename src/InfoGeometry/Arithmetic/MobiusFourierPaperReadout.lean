import InfoGeometry.Arithmetic.MobiusFourierLocalMoment
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Paper-facing readout for finite Möbius Fourier polynomials

This file records the direct finite sum and the rooted local moment used in
the paper.  It contains no limiting statement, asymptotic estimate, or
Riemann-hypothesis assertion.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.MobiusFourierPaperReadout

open InfoGeometry.Arithmetic.MobiusFourierLocalMoment
open InfoGeometry.Arithmetic.PrimeBitFiniteMobiusPolynomial

/-- The unnormalised finite Möbius Fourier sum. -/
def mobiusFourierSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.moebius n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ))

/-- The finite polynomial with the paper's `N⁻¹ᐟ²` normalization. -/
def paperMobiusFourierPolynomial (N : ℕ) (t : ℝ) : ℂ :=
  (Real.rpow (N : ℝ) (-1 / 2) : ℂ) • mobiusFourierSum N t

theorem primeCutoffMobiusPolynomial_eq_mobiusFourierSum
    (N : ℕ) (t : ℝ) :
    primeCutoffMobiusPolynomial N
        (fun n => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) =
      mobiusFourierSum N t := by
  rw [primeCutoffMobiusPolynomial_eq_integerCutoff]
  rfl

theorem mobiusFourierPolynomial_eq_paperMobiusFourierPolynomial
    (N : ℕ) (t : ℝ) :
    mobiusFourierPolynomial N t = paperMobiusFourierPolynomial N t := by
  rw [mobiusFourierPolynomial, paperMobiusFourierPolynomial]
  rw [primeCutoffMobiusPolynomial_eq_mobiusFourierSum]

theorem paperMobiusFourierPolynomial_zero (N : ℕ) :
    paperMobiusFourierPolynomial N 0 =
      (Real.rpow (N : ℝ) (-1 / 2) : ℂ) •
        (MobiusMertensRHEquivalence.mertensFunction N : ℂ) := by
  rw [← mobiusFourierPolynomial_eq_paperMobiusFourierPolynomial]
  exact mobiusFourierPolynomial_zero N

theorem norm_paperMobiusFourierPolynomial_zero (N : ℕ) :
    ‖paperMobiusFourierPolynomial N 0‖ =
      Real.rpow (N : ℝ) (-1 / 2) *
        |MobiusMertensRHEquivalence.mertensFunction N| := by
  rw [paperMobiusFourierPolynomial_zero]
  simp [Complex.norm_real, abs_of_nonneg (Real.rpow_nonneg _ _)]

theorem localMomentIntegral_eq_scaled_unnormalized
    (N q : ℕ) (c : ℝ) :
    localMomentIntegral N q c =
      (N : ℝ) / (2 * c) *
        (Real.rpow (N : ℝ) (-1 / 2)) ^ q *
          (∫ t in (-c / (N : ℝ))..(c / (N : ℝ)),
            ‖mobiusFourierSum N t‖ ^ q) := by
  unfold localMomentIntegral mobiusFourierPolynomial
  rw [show (fun t : ℝ =>
      ‖(Real.rpow (N : ℝ) (-1 / 2) : ℂ) •
        primeCutoffMobiusPolynomial N
          (fun n => Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)))‖ ^ q) =
      (fun t : ℝ =>
        (Real.rpow (N : ℝ) (-1 / 2)) ^ q * ‖mobiusFourierSum N t‖ ^ q) by
    funext t
    rw [primeCutoffMobiusPolynomial_eq_mobiusFourierSum]
    simp [Complex.norm_real, abs_of_nonneg (Real.rpow_nonneg _ _), mul_pow]]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The rooted local moment corresponding to a positive integer `q`.

The proof `hq` is part of the definition so that the paper's finite-moment
domain is explicit.  No positivity or asymptotic theorem is asserted here.
-/
def rootedLocalMoment (N q : ℕ) (c : ℝ) (hq : 0 < q) : ℝ :=
  Real.rpow (localMomentIntegral N q c) (1 / (q : ℝ))

/-- Explicit paper-normalized form of the rooted finite local moment. -/
theorem rootedLocalMoment_eq_paper_integral
    (N q : ℕ) (c : ℝ) (hq : 0 < q) :
    rootedLocalMoment N q c hq =
      Real.rpow
        ((N : ℝ) / (2 * c) *
          ∫ t in (-c / (N : ℝ))..(c / (N : ℝ)),
            ‖mobiusFourierPolynomial N t‖ ^ q)
        (1 / (q : ℝ)) := by
  rfl

end InfoGeometry.Arithmetic.MobiusFourierPaperReadout
