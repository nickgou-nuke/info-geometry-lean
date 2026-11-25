/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.FermiDiracAnalytic
import InfoGeometry.Krein.TomitaMatrixAtom
import InfoGeometry.Lie.LorentzCartanKernel
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Real single-mode Gibbs algebra at a co-rotating energy threshold

The creation, annihilation, number, hole and swap operators are the existing
real `TomitaMatrixAtom` operators. We normalize their two-state Gibbs matrix,
identify its occupation with the existing Fermi function, and specialize the
Massieu, susceptibility and entropy results to `x = β * (E - Ω * m)`.

The separate Lorentz coordinate kernel lemma is a stabilizer calculation.
It does not identify the kernel with the zero-exponent threshold: the final
theorem gives an explicit counterexample. No spacetime CPT, scattering,
greybody factor, or geometric horizon identification is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.KerrUnruhFermionicHorizonBridge

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Krein.TomitaMatrixAtom
open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
open InfoGeometry.Lie.LorentzCartanKernel

/-- The positive, unnormalized Gibbs weight on the existing real two-state atom. -/
def fockGibbsMatrix (x : ℝ) : Mat2R := Real.exp (-x) • Pplus + Pminus

/-- The normalized two-state density matrix. -/
def fockGibbsDensity (x : ℝ) : Mat2R :=
  (Matrix.trace (fockGibbsMatrix x))⁻¹ • fockGibbsMatrix x

/-- Co-rotating exponent; the assignment of physical units is external. -/
def kerrExponent (β Ω E m : ℝ) : ℝ := β * (E - Ω * m)

/-- Specialization of the existing Fermi occupation to co-rotating energy. -/
def kerrFermiOcc (β Ω E m : ℝ) : ℝ := fermiOccupation β (E - Ω * m)

theorem kerrFermiOcc_eq_dimensionless (β Ω E m : ℝ) :
    kerrFermiOcc β Ω E m = fermiOccupation 1 (kerrExponent β Ω E m) := by
  simp [kerrFermiOcc, kerrExponent, fermiOccupation]

theorem kerrFermiOcc_eq_inv (β Ω E m : ℝ) :
    kerrFermiOcc β Ω E m = (1 + Real.exp (β * (E - Ω * m)))⁻¹ := by
  simp [kerrFermiOcc, fermiOccupation, one_div, add_comm]

theorem trace_fockGibbsMatrix (x : ℝ) :
    Matrix.trace (fockGibbsMatrix x) = 1 + Real.exp (-x) := by
  simp [fockGibbsMatrix, Pplus, Pminus, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, add_comm]

theorem trace_fockGibbsMatrix_pos (x : ℝ) : 0 < Matrix.trace (fockGibbsMatrix x) := by
  rw [trace_fockGibbsMatrix]
  positivity

/-- The differentiated Massieu function is the logarithm of this operator partition trace. -/
theorem fermiMassieu_eq_log_trace (x : ℝ) :
    fermiMassieu x = Real.log (Matrix.trace (fockGibbsMatrix x)) := by
  rw [trace_fockGibbsMatrix]
  rfl

theorem trace_number_mul_fockGibbsMatrix (x : ℝ) :
    Matrix.trace (Pplus * fockGibbsMatrix x) = Real.exp (-x) := by
  rw [fockGibbsMatrix, mul_add, mul_smul_comm, Pplus_idempotent,
    Pplus_mul_Pminus, add_zero]
  simp [Pplus, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- The normalized operator expectation agrees with the real Fermi occupation. -/
theorem fockGibbs_expectation (x : ℝ) :
    Matrix.trace (Pplus * fockGibbsMatrix x) / Matrix.trace (fockGibbsMatrix x) =
      fermiOccupation 1 x := by
  rw [trace_number_mul_fockGibbsMatrix, trace_fockGibbsMatrix]
  exact (fermiOccupation_one_eq_weight x).symm

theorem fockGibbsDensity_eq_weighted_projectors (x : ℝ) :
    fockGibbsDensity x =
      fermiOccupation 1 x • Pplus + (1 - fermiOccupation 1 x) • Pminus := by
  have hden : 1 + Real.exp (-x) ≠ 0 := by positivity
  have hn : (1 + Real.exp (-x))⁻¹ * Real.exp (-x) = fermiOccupation 1 x := by
    rw [fermiOccupation_one_eq_weight, div_eq_mul_inv, mul_comm]
  have hh : (1 + Real.exp (-x))⁻¹ = 1 - fermiOccupation 1 x := by
    rw [fermiOccupation_one_eq_weight]
    field_simp [hden]
    ring
  rw [fockGibbsDensity, trace_fockGibbsMatrix, fockGibbsMatrix,
    smul_add, smul_smul, hn, hh]

/-- The positive polarization weight at contrast `2n-1` is `n`. -/
theorem thermalWeightPlus_fermi (x : ℝ) :
    thermalWeightPlus (2 * fermiOccupation 1 x - 1) = fermiOccupation 1 x := by
  unfold thermalWeightPlus
  ring

theorem thermalWeightMinus_fermi (x : ℝ) :
    thermalWeightMinus (2 * fermiOccupation 1 x - 1) = 1 - fermiOccupation 1 x := by
  unfold thermalWeightMinus
  ring

theorem fermi_contrast_bounds (x : ℝ) :
    -1 ≤ 2 * fermiOccupation 1 x - 1 ∧ 2 * fermiOccupation 1 x - 1 ≤ 1 := by
  have hp := fermiOccupation_pos 1 x
  have hq := fermiOccupation_lt_one 1 x
  constructor <;> linarith

/-- The Gibbs state is the existing thermal polarization at contrast `2n-1`. -/
theorem fockGibbsDensity_eq_thermalPolarization (x : ℝ) :
    fockGibbsDensity x = thermalPolarization (2 * fermiOccupation 1 x - 1) := by
  rw [fockGibbsDensity_eq_weighted_projectors,
    thermalPolarization_eq_weighted_projectors, thermalWeightPlus_fermi,
    thermalWeightMinus_fermi]

theorem trace_fockGibbsDensity (x : ℝ) : Matrix.trace (fockGibbsDensity x) = 1 := by
  rw [fockGibbsDensity_eq_thermalPolarization, thermalPolarization_trace]

theorem fockGibbsDensity_posSemidef (x : ℝ) : Matrix.PosSemidef (fockGibbsDensity x) := by
  rw [fockGibbsDensity_eq_thermalPolarization, thermalPolarization_posSemidef_iff]
  exact fermi_contrast_bounds x

theorem trace_number_mul_fockGibbsDensity (x : ℝ) :
    Matrix.trace (Pplus * fockGibbsDensity x) = fermiOccupation 1 x := by
  rw [fockGibbsDensity_eq_weighted_projectors, mul_add,
    mul_smul_comm, mul_smul_comm, Pplus_idempotent, Pplus_mul_Pminus]
  simp [Pplus, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Particle–hole exchange is actual conjugation by the existing real swap. -/
theorem fockGibbsDensity_particle_hole (x : ℝ) :
    J * fockGibbsDensity x * J = fockGibbsDensity (-x) := by
  rw [fockGibbsDensity_eq_weighted_projectors,
    fockGibbsDensity_eq_weighted_projectors, fermiOccupation_one_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Pplus, Pminus, Matrix.mul_apply, Fin.sum_univ_two]

theorem kerr_gibbs_expectation (β Ω E m : ℝ) :
    Matrix.trace (Pplus * fockGibbsMatrix (kerrExponent β Ω E m)) /
      Matrix.trace (fockGibbsMatrix (kerrExponent β Ω E m)) =
        kerrFermiOcc β Ω E m := by
  rw [fockGibbs_expectation, kerrFermiOcc_eq_dimensionless]

theorem kerrFermiOcc_bounds (β Ω E m : ℝ) :
    0 < kerrFermiOcc β Ω E m ∧ kerrFermiOcc β Ω E m < 1 :=
  ⟨fermiOccupation_pos β (E - Ω * m), fermiOccupation_lt_one β (E - Ω * m)⟩

/-- Positivity of the stipulated inverse-temperature calibration at positive surface gravity. -/
theorem calibrated_inverseTemperature_pos (κ : ℝ) (hκ : 0 < κ) :
    0 < (2 * Real.pi) / κ :=
  div_pos (mul_pos (by norm_num) Real.pi_pos) hκ

theorem kerrExponent_neg_beta (β Ω E m : ℝ) :
    kerrExponent (-β) Ω E m = -kerrExponent β Ω E m := by
  unfold kerrExponent
  ring

theorem kerrExponent_neg_charges (β Ω E m : ℝ) :
    kerrExponent β Ω (-E) (-m) = -kerrExponent β Ω E m := by
  unfold kerrExponent
  ring

theorem kerrFermiOcc_neg_beta (β Ω E m : ℝ) :
    kerrFermiOcc (-β) Ω E m = 1 - kerrFermiOcc β Ω E m := by
  rw [kerrFermiOcc_eq_dimensionless, kerrExponent_neg_beta,
    fermiOccupation_one_neg, kerrFermiOcc_eq_dimensionless]

theorem kerrFermiOcc_neg_charges (β Ω E m : ℝ) :
    kerrFermiOcc β Ω (-E) (-m) = 1 - kerrFermiOcc β Ω E m := by
  rw [kerrFermiOcc_eq_dimensionless, kerrExponent_neg_charges,
    fermiOccupation_one_neg, kerrFermiOcc_eq_dimensionless]

theorem kerrExponent_eq_zero_iff (β Ω E m : ℝ) (hβ : 0 < β) :
    kerrExponent β Ω E m = 0 ↔ E = Ω * m := by
  unfold kerrExponent
  rw [mul_eq_zero, or_iff_right (ne_of_gt hβ), sub_eq_zero]

theorem kerrFermiOcc_eq_half_iff (β Ω E m : ℝ) (hβ : 0 < β) :
    kerrFermiOcc β Ω E m = 1 / 2 ↔ E = Ω * m := by
  rw [kerrFermiOcc_eq_dimensionless, fermiOccupation_one_eq_half_iff,
    kerrExponent_eq_zero_iff β Ω E m hβ]

/-- Specialization to `β = 2π/κ`; this uses the calibration rather than deriving a spacetime law. -/
theorem calibrated_kerrFermiOcc_eq_half_iff (κ Ω E m : ℝ) (hκ : 0 < κ) :
    kerrFermiOcc ((2 * Real.pi) / κ) Ω E m = 1 / 2 ↔ E = Ω * m :=
  kerrFermiOcc_eq_half_iff ((2 * Real.pi) / κ) Ω E m
    (calibrated_inverseTemperature_pos κ hκ)

theorem kerrFermiOcc_lt_half_iff (β Ω E m : ℝ) (hβ : 0 < β) :
    kerrFermiOcc β Ω E m < 1 / 2 ↔ Ω * m < E := by
  rw [kerrFermiOcc_eq_dimensionless, fermiOccupation_one_lt_half_iff]
  unfold kerrExponent
  rw [mul_pos_iff_of_pos_left hβ, sub_pos]

theorem half_lt_kerrFermiOcc_iff (β Ω E m : ℝ) (hβ : 0 < β) :
    1 / 2 < kerrFermiOcc β Ω E m ↔ E < Ω * m := by
  rw [kerrFermiOcc_eq_dimensionless, half_lt_fermiOccupation_one_iff]
  unfold kerrExponent
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_neg_of_pos_of_neg hβ (sub_neg.mpr h)

/-- The susceptibility and entropy reach their sharp maxima at zero co-rotating energy. -/
theorem kerr_susceptibility_entropy_peaks (β Ω E m : ℝ) (hβ : 0 < β) :
    (fermiSusceptibility (kerrExponent β Ω E m) = 1 / 4 ↔ E = Ω * m) ∧
      (Real.binEntropy (kerrFermiOcc β Ω E m) = Real.log 2 ↔ E = Ω * m) := by
  rw [fermiSusceptibility_eq_quarter_iff, kerrFermiOcc_eq_dimensionless,
    fermiEntropy_eq_log_two_iff, kerrExponent_eq_zero_iff β Ω E m hβ]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The Souriau-style coordinate pairing and kernel equation are distinct identities. -/
theorem kerr_pairing_and_cartan_kernel (β Ω E m : ℝ) :
    dotProduct (modeCharge E m) (rotatingTemperature β Ω) = kerrExponent β Ω E m ∧
      (lorentzPoissonMat 0 0 m 0 0 E).mulVec (rotatingTemperature β Ω) = 0 :=
  ⟨modeCharge_dot_rotatingTemperature β Ω E m,
    rotatingTemperature_mem_kernel β Ω E m⟩

/-- Kernel membership does not force half occupation, even for positive inverse temperature. -/
theorem cartan_kernel_not_half_occupation :
    (lorentzPoissonMat 0 0 0 0 0 1).mulVec (rotatingTemperature 1 0) = 0 ∧
      dotProduct (modeCharge 1 0) (rotatingTemperature 1 0) = 1 ∧
      kerrFermiOcc 1 0 1 0 < 1 / 2 := by
  refine ⟨kernel_pairing_counterexample.1, kernel_pairing_counterexample.2, ?_⟩
  exact (kerrFermiOcc_lt_half_iff 1 0 1 0 (by norm_num)).2 (by norm_num)

end InfoGeometry.Canonical.KerrUnruhFermionicHorizonBridge
