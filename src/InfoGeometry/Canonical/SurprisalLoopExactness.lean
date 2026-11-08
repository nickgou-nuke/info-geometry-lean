import InfoGeometry.Analysis.LogVolumePathIntegral
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteBogoliubovFrameDeformationEntropy

/-!
# Exact logarithmic matrix-volume loops

This file separates globally exact logarithmic volume forms from nontrivial
winding classes.  A closed finite matrix path whose determinant norm admits
the global logarithmic differential has zero period.  Consequently any
integer appearing through the usual `2πi` normalization is forced to be zero.

Nonzero winding belongs to a punctured complex determinant loop and cannot be
deduced from endpoint periodicity of a globally defined logarithm.
-/

noncomputable section

namespace InfoGeometry.Canonical.SurprisalLoopExactness

open MeasureTheory
open scoped Interval
open InfoGeometry.Analysis.LogVolumeEntropyRate
open InfoGeometry.Analysis.LogVolumeExactDifferential
open InfoGeometry.Analysis.LogVolumePathIntegral

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- Positive scalar volume path read from a complex matrix determinant. -/
def determinantNormPath (Delta : ℝ → Mat) : ℝ → ℝ :=
  fun t => ‖(Delta t).det‖

/-- Global logarithmic determinant-volume one-form along a matrix path. -/
def determinantLogVolumeOneForm (Delta : ℝ → Mat) : ℝ → ℝ :=
  logVolumeDifferential (determinantNormPath Delta)

/-- Negative logarithmic determinant-volume form, matching surprisal orientation. -/
def determinantSurprisalOneForm (Delta : ℝ → Mat) : ℝ → ℝ :=
  fun t => -determinantLogVolumeOneForm Delta t

/--
A closed matrix path has zero period for its globally defined logarithmic
determinant-volume form.
-/
theorem integral_determinantLogVolumeOneForm_eq_zero_of_closed
    {Delta : ℝ → Mat} {a b : ℝ}
    (hDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (determinantNormPath Delta) t)
    (hNonzero :
      ∀ t ∈ Set.uIcc a b,
        determinantNormPath Delta t ≠ 0)
    (hInt :
      IntervalIntegrable
        (determinantLogVolumeOneForm Delta)
        volume a b)
    (hClosed : Delta b = Delta a) :
    ∫ t in a..b, determinantLogVolumeOneForm Delta t = 0 := by
  apply integral_logVolumeDifferential_eq_zero_of_endpoints_eq
    hDiff hNonzero hInt
  simp only [determinantNormPath]
  rw [hClosed]

/--
The surprisal-oriented negative logarithmic form also has zero period on a
closed matrix path.
-/
theorem integral_determinantSurprisalOneForm_eq_zero_of_closed
    {Delta : ℝ → Mat} {a b : ℝ}
    (hDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (determinantNormPath Delta) t)
    (hNonzero :
      ∀ t ∈ Set.uIcc a b,
        determinantNormPath Delta t ≠ 0)
    (hInt :
      IntervalIntegrable
        (determinantLogVolumeOneForm Delta)
        volume a b)
    (hClosed : Delta b = Delta a) :
    ∫ t in a..b, determinantSurprisalOneForm Delta t = 0 := by
  rw [show determinantSurprisalOneForm Delta =
      fun t => -determinantLogVolumeOneForm Delta t by
    rfl]
  rw [intervalIntegral.integral_neg,
    integral_determinantLogVolumeOneForm_eq_zero_of_closed
      hDiff hNonzero hInt hClosed]
  simp

/--
The normalized period of a globally exact closed determinant-surprisal form
has the integer representative `0`.
-/
theorem normalized_closed_surprisal_period_exists_integer
    {Delta : ℝ → Mat} {a b : ℝ}
    (hDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (determinantNormPath Delta) t)
    (hNonzero :
      ∀ t ∈ Set.uIcc a b,
        determinantNormPath Delta t ≠ 0)
    (hInt :
      IntervalIntegrable
        (determinantLogVolumeOneForm Delta)
        volume a b)
    (hClosed : Delta b = Delta a) :
    ∃ w : ℤ,
      (1 / (2 * Real.pi * Complex.I : ℂ)) *
          (∫ t in a..b, determinantSurprisalOneForm Delta t : ℂ) =
        (w : ℂ) := by
  refine ⟨0, ?_⟩
  rw [intervalIntegral.integral_ofReal,
    integral_determinantSurprisalOneForm_eq_zero_of_closed
    hDiff hNonzero hInt hClosed]
  simp

/--
Any integer assigned to the normalized period of a globally exact closed
determinant-surprisal form is necessarily zero.
-/
theorem normalized_closed_surprisal_period_integer_eq_zero
    {Delta : ℝ → Mat} {a b : ℝ} {w : ℤ}
    (hDiff :
      ∀ t ∈ Set.uIcc a b,
        DifferentiableAt ℝ (determinantNormPath Delta) t)
    (hNonzero :
      ∀ t ∈ Set.uIcc a b,
        determinantNormPath Delta t ≠ 0)
    (hInt :
      IntervalIntegrable
        (determinantLogVolumeOneForm Delta)
        volume a b)
    (hClosed : Delta b = Delta a)
    (hPeriod :
      (1 / (2 * Real.pi * Complex.I : ℂ)) *
          (∫ t in a..b, determinantSurprisalOneForm Delta t : ℂ) =
        (w : ℂ)) :
    w = 0 := by
  rw [intervalIntegral.integral_ofReal,
    integral_determinantSurprisalOneForm_eq_zero_of_closed
    hDiff hNonzero hInt hClosed] at hPeriod
  have hwComplex : (w : ℂ) = 0 := by
    simpa using hPeriod.symm
  exact_mod_cast hwComplex

/-! ## Finite trace obstruction to a commutator identification -/

/-- Matrix commutator in the finite complex carrier. -/
def matrixCommutator (A B : Mat) : Mat :=
  A * B - B * A

omit [DecidableEq n] in
/-- The ordinary finite matrix trace annihilates every commutator. -/
theorem trace_matrixCommutator (A B : Mat) :
    Matrix.trace (matrixCommutator A B) = 0 := by
  rw [matrixCommutator, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

omit [DecidableEq n] in
/--
If an operator-valued one-form is pointwise a finite matrix commutator, then
its ordinary trace vanishes pointwise.
-/
theorem trace_oneForm_eq_zero_of_eq_commutator
    (omega Pforward Pbackward : ℝ → Mat)
    (hComm :
      ∀ t : ℝ,
        omega t = matrixCommutator (Pforward t) (Pbackward t)) :
    ∀ t : ℝ, Matrix.trace (omega t) = 0 := by
  intro t
  rw [hComm t, trace_matrixCommutator]

omit [DecidableEq n] in
/--
The traced period of a one-form represented pointwise by finite matrix
commutators is zero on every interval.
-/
theorem integral_trace_oneForm_eq_zero_of_eq_commutator
    (omega Pforward Pbackward : ℝ → Mat)
    (a b : ℝ)
    (hComm :
      ∀ t : ℝ,
        omega t = matrixCommutator (Pforward t) (Pbackward t)) :
    ∫ t in a..b, Matrix.trace (omega t) = 0 := by
  calc
    (∫ t in a..b, Matrix.trace (omega t)) =
        ∫ _t in a..b, (0 : ℂ) := by
          apply intervalIntegral.integral_congr
          intro t _
          exact trace_oneForm_eq_zero_of_eq_commutator
            omega Pforward Pbackward hComm t
    _ = 0 := intervalIntegral.integral_zero

omit [DecidableEq n] in
/--
Therefore a winding integer extracted from the ordinary trace of a finite
commutator-valued one-form is necessarily zero.
-/
theorem normalized_commutator_period_integer_eq_zero
    (omega Pforward Pbackward : ℝ → Mat)
    (a b : ℝ) (w : ℤ)
    (hComm :
      ∀ t : ℝ,
        omega t = matrixCommutator (Pforward t) (Pbackward t))
    (hPeriod :
      (1 / (2 * Real.pi * Complex.I : ℂ)) *
          (∫ t in a..b, Matrix.trace (omega t)) =
        (w : ℂ)) :
    w = 0 := by
  rw [integral_trace_oneForm_eq_zero_of_eq_commutator
    omega Pforward Pbackward a b hComm] at hPeriod
  have hwComplex : (w : ℂ) = 0 := by
    simpa using hPeriod.symm
  exact_mod_cast hwComplex

end InfoGeometry.Canonical.SurprisalLoopExactness
