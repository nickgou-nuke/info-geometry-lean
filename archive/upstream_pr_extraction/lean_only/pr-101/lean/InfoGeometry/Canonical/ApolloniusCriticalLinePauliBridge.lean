import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.HestenesPauliSheetBridge

/-!
# Apollonius critical-line / circular Pauli bridge

This file formalizes the exact elementary geometry behind the marked pair
`0,1` in the zeta affine coordinate and joins it to the repository-owned
circular Pauli/Hestenes ladder basis.

The theorem-honest content is:

* equality of squared Euclidean distances from `s` to `0` and `1` is exactly
  `Re(s)=1/2`;
* the corresponding normalized Apollonius squared-distance ratio is `1` on
  that line, hence its logarithmic potential is zero there;
* the circular ladder matrices close under commutator on the parity generator.

No statement about zeros of the Riemann zeta function, flux quantization,
Hilbert--Polya, or the Riemann hypothesis is asserted.  Those require
independent analytic/spectral theorems not supplied by these identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusCriticalLinePauliBridge

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Canonical.HestenesPauliSheetBridge

/-- Squared Euclidean distance of `s = σ + iτ` from the marked point `0`. -/
def distSqZero (s : ℂ) : ℝ :=
  s.re ^ 2 + s.im ^ 2

/-- Squared Euclidean distance of `s = σ + iτ` from the marked point `1`. -/
def distSqOne (s : ℂ) : ℝ :=
  (s.re - 1) ^ 2 + s.im ^ 2

/-- Signed Apollonius balance for the marked pair `0,1`. -/
def apolloniusBalance (s : ℂ) : ℝ :=
  distSqZero s - distSqOne s

/-- The signed distance-square balance is the centered real coordinate,
up to the exact factor `2`. -/
theorem apolloniusBalance_eq_two_re_sub_one (s : ℂ) :
    apolloniusBalance s = 2 * s.re - 1 := by
  unfold apolloniusBalance distSqZero distSqOne
  ring

/-- A point is equidistant from `0` and `1` exactly when its real coordinate
is `1/2`.  This is the precise Apollonius/equipotential statement. -/
theorem equidistant_zero_one_iff_criticalLine (s : ℂ) :
    distSqZero s = distSqOne s ↔ CriticalLine s := by
  rw [criticalLine_iff_re_eq_half]
  unfold distSqZero distSqOne
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- The Apollonius balance vanishes exactly on the critical line. -/
theorem apolloniusBalance_eq_zero_iff_criticalLine (s : ℂ) :
    apolloniusBalance s = 0 ↔ CriticalLine s := by
  rw [apolloniusBalance_eq_two_re_sub_one, criticalLine_iff_re_eq_half]
  constructor <;> intro h <;> linarith

/-- Squared-distance Apollonius ratio.  This is positive away from the marked
point `1`; its logarithm is the elementary dipole potential used below. -/
def apolloniusRatioSq (s : ℂ) : ℝ :=
  distSqZero s / distSqOne s

/-- The denominator of the Apollonius ratio is strictly positive on the
critical line. -/
theorem distSqOne_pos_of_criticalLine {s : ℂ} (hs : CriticalLine s) :
    0 < distSqOne s := by
  rw [criticalLine_iff_re_eq_half] at hs
  unfold distSqOne
  rw [hs]
  have him : 0 ≤ s.im ^ 2 := sq_nonneg s.im
  nlinarith

/-- On the critical line the normalized squared-distance ratio is exactly one. -/
theorem apolloniusRatioSq_eq_one_of_criticalLine {s : ℂ}
    (hs : CriticalLine s) :
    apolloniusRatioSq s = 1 := by
  have heq : distSqZero s = distSqOne s :=
    (equidistant_zero_one_iff_criticalLine s).2 hs
  have hne : distSqOne s ≠ 0 := ne_of_gt (distSqOne_pos_of_criticalLine hs)
  unfold apolloniusRatioSq
  rw [heq]
  exact div_self hne

/-- Elementary logarithmic Apollonius potential associated with the marked
pair `0,1`. -/
def apolloniusLogPotential (s : ℂ) : ℝ :=
  Real.log (apolloniusRatioSq s)

/-- The logarithmic Apollonius potential vanishes on the critical line. -/
theorem apolloniusLogPotential_eq_zero_of_criticalLine {s : ℂ}
    (hs : CriticalLine s) :
    apolloniusLogPotential s = 0 := by
  unfold apolloniusLogPotential
  rw [apolloniusRatioSq_eq_one_of_criticalLine hs]
  exact Real.log_one

/-- Ordinary matrix commutator. -/
def matrixCommutator (A B : M2C) : M2C :=
  A * B - B * A

/-- The circular raising/lowering commutator is exactly the Hestenes parity
operator.  Together with the already-proved anticommutator this gives the
finite circular Pauli ladder algebra. -/
theorem circular_commutator :
    matrixCommutator circularPlus circularMinus = hestenesParity := by
  unfold matrixCommutator
  rw [circularPlus_mul_circularMinus, circularMinus_mul_circularPlus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [hestenesScalar, hestenesParity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetIdentity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply] <;> ring

/-- The parity generator acts with weight `+2` on the circular raising rail. -/
theorem parity_circularPlus_commutator :
    matrixCommutator hestenesParity circularPlus =
      (2 : ℂ) • circularPlus := by
  rw [circularPlus_eq_sigmaPlus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, hestenesParity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity,
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sigmaPlus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- The parity generator acts with weight `-2` on the circular lowering rail. -/
theorem parity_circularMinus_commutator :
    matrixCommutator hestenesParity circularMinus =
      (-2 : ℂ) • circularMinus := by
  rw [circularMinus_eq_sigmaMinus]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, hestenesParity,
      InfoGeometry.Canonical.ChiralStokesPauliBasis.sheetParity,
      InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sigmaMinus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- Consolidated exact packet: the geometric ground locus and the circular
ladder algebra coexist without any additional arithmetic-zero hypothesis. -/
theorem apollonius_pauli_exact_packet (s : ℂ) :
    (distSqZero s = distSqOne s ↔ CriticalLine s) ∧
    matrixCommutator circularPlus circularMinus = hestenesParity ∧
    circularPlus * circularMinus + circularMinus * circularPlus =
      hestenesScalar := by
  exact ⟨equidistant_zero_one_iff_criticalLine s,
    circular_commutator,
    circular_anticommutator⟩

end InfoGeometry.Canonical.ApolloniusCriticalLinePauliBridge
