import InfoGeometry.Arithmetic.MobiusFiniteAbelSummation
import InfoGeometry.Arithmetic.MobiusFourierPaperReadout

/-!
# Finite Möbius Fourier--Abel bridge

This owner specializes finite Abel summation to the paper-facing Möbius Fourier
phase.  It remains entirely finite and makes no claim about an integral
partial-summation formula or asymptotic bounds.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.MobiusFourierFiniteAbelBridge

open InfoGeometry.Arithmetic.MobiusFiniteAbelSummation
open InfoGeometry.Arithmetic.MobiusFourierPaperReadout
open InfoGeometry.Arithmetic.MobiusMertensRHEquivalence

def fourierPhase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ))

theorem mobiusFourierSum_zero (N : ℕ) :
    mobiusFourierSum N 0 =
      (mertensFunction N : ℂ) := by
  unfold mobiusFourierSum
  simpa [Complex.exp_zero, mertensFunction] using
    (mobius_sum_range_eq_Icc_complex (fun _ => (1 : ℂ)) N).symm

theorem mobiusFourierSum_eq_mertens_finiteAbel
    (N : ℕ) (t : ℝ) :
    mobiusFourierSum N t =
      (mertensFunction N : ℂ) * fourierPhase t N +
        ∑ n ∈ Finset.range N,
          (mertensFunction n : ℂ) *
            (fourierPhase t n - fourierPhase t (n + 1)) := by
  change (∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ) * fourierPhase t n) = _
  rw [← mobius_sum_range_eq_Icc_complex (fourierPhase t) N]
  exact mobius_sum_eq_mertens_summation_by_parts_complex
    (fourierPhase t) N

theorem fourierPhase_difference_factor (t : ℝ) (n : ℕ) :
    fourierPhase t n - fourierPhase t (n + 1) =
      fourierPhase t n * (1 - fourierPhase t 1) := by
  unfold fourierPhase
  rw [show 2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * (t : ℂ) =
      (2 * Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) +
        (2 * Real.pi * Complex.I * (1 : ℂ) * (t : ℂ)) by
    push_cast
    ring]
  rw [Complex.exp_add]
  ring

theorem mobiusFourierSum_eq_mertens_finiteAbel_factorized
    (N : ℕ) (t : ℝ) :
    mobiusFourierSum N t =
      (mertensFunction N : ℂ) * fourierPhase t N +
        (1 - fourierPhase t 1) *
          ∑ n ∈ Finset.range N,
            (mertensFunction n : ℂ) * fourierPhase t n := by
  rw [mobiusFourierSum_eq_mertens_finiteAbel]
  rw [show (∑ n ∈ Finset.range N,
      (mertensFunction n : ℂ) *
        (fourierPhase t n - fourierPhase t (n + 1))) =
      (1 - fourierPhase t 1) *
        ∑ n ∈ Finset.range N,
          (mertensFunction n : ℂ) * fourierPhase t n by
    simp_rw [fourierPhase_difference_factor]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring]

end InfoGeometry.Arithmetic.MobiusFourierFiniteAbelBridge
