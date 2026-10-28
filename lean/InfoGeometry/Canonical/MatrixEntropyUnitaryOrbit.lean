/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PolarFrameTraceDensity
import InfoGeometry.Canonical.QuantumRelativeSurprisal
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # Actual matrix entropy under unitary conjugation and trace normalization

The existing entropy trace expression is instantiated with the native CFC
logarithm. The density-weighted entropy remains distinct from an unweighted
trace logarithm or a logdet barrier. These are symmetry and normalization
identities on full complex matrices; they assert no spectral gap.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open PolarFrameTraceDensity

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The real entropy expression with its actual operator logarithm. -/
def matrixEntropy (P : Mat) : ℝ :=
  (QuantumRelativeSurprisal.vonNeumannEntropy P (CFC.log P)).re

theorem matrixEntropy_eq (P : Mat) :
    matrixEntropy P = -(Matrix.trace (P * CFC.log P)).re := rfl

theorem matrixEntropy_eq_trace_negative_log (P : Mat) :
    matrixEntropy P = (Matrix.trace (P * (-CFC.log P))).re := by
  simp [matrixEntropy_eq, mul_neg]

theorem trace_unitary_conjugate (U : unitary Mat) (P : Mat) :
    Matrix.trace ((U : Mat) * P * star (U : Mat)) = Matrix.trace P := by
  rw [Matrix.trace_mul_cycle]
  simp

/-- CFC naturality for the exact unitary algebra automorphism. -/
theorem log_unitary_conjugate (U : unitary Mat) (P : Mat)
    (hP : IsStrictlyPositive P) :
    CFC.log ((U : Mat) * P * star (U : Mat)) =
      (U : Mat) * CFC.log P * star (U : Mat) := by
  let φ := Unitary.conjStarAlgAut ℝ Mat U
  have hf : ContinuousOn Real.log (spectrum ℝ P) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hP.spectrum_pos hx)
  have hφ : Continuous φ := by
    change Continuous (fun X : Mat => (U : Mat) * X * star (U : Mat))
    fun_prop
  simpa only [CFC.log, φ, Unitary.conjStarAlgAut_apply] using
    (StarAlgHomClass.map_cfc φ Real.log P hf hφ hP.isSelfAdjoint
      (hP.isSelfAdjoint.map φ)).symm

/-- Unitary orbit motion leaves the actual matrix entropy constant. -/
theorem matrixEntropy_unitary_conjugate (U : unitary Mat) (P : Mat)
    (hP : IsStrictlyPositive P) :
    matrixEntropy ((U : Mat) * P * star (U : Mat)) = matrixEntropy P := by
  simp only [matrixEntropy_eq, log_unitary_conjugate U P hP]
  have hmul :
      ((U : Mat) * P * star (U : Mat)) *
          ((U : Mat) * CFC.log P * star (U : Mat)) =
        (U : Mat) * (P * CFC.log P) * star (U : Mat) := by
    simpa only [Unitary.conjStarAlgAut_apply] using
      (map_mul (Unitary.conjStarAlgAut ℝ Mat U) P (CFC.log P)).symm
  rw [hmul, trace_unitary_conjugate]

/-- Trace normalization commutes with conjugation on the same matrix carrier. -/
theorem normalizedDensity_unitary_conjugate (U : unitary Mat) (P : Mat) :
    normalizedDensity ((U : Mat) * P * star (U : Mat)) =
      (U : Mat) * normalizedDensity P * star (U : Mat) := by
  simp [normalizedDensity, traceMass, trace_unitary_conjugate]

/-- The density weight gives this entropy normalization correction, without a dimension factor. -/
theorem matrixEntropy_normalizedDensity [Nonempty n]
    (P : Mat) (hP : IsStrictlyPositive P) :
    matrixEntropy (normalizedDensity P) =
      (traceMass P)⁻¹ * matrixEntropy P + Real.log (traceMass P) := by
  rw [matrixEntropy_eq_trace_negative_log, neg_log_normalizedDensity P hP,
    mul_add, Matrix.trace_add, Complex.add_re]
  have hfirst :
      (Matrix.trace (normalizedDensity P * (-CFC.log P))).re =
        (traceMass P)⁻¹ * matrixEntropy P := by
    simp [normalizedDensity, Matrix.trace_smul,
      matrixEntropy_eq_trace_negative_log]
  have hsecond :
      (Matrix.trace (normalizedDensity P *
        (Real.log (traceMass P) • (1 : Mat)))).re = Real.log (traceMass P) := by
    simp [Matrix.trace_smul, trace_normalizedDensity P hP]
  rw [hfirst, hsecond]

theorem matrixEntropy_normalized_unitary_conjugate [Nonempty n]
    (U : unitary Mat) (P : Mat) (hP : IsStrictlyPositive P) :
    matrixEntropy (normalizedDensity ((U : Mat) * P * star (U : Mat))) =
      matrixEntropy (normalizedDensity P) := by
  rw [normalizedDensity_unitary_conjugate]
  exact matrixEntropy_unitary_conjugate U (normalizedDensity P)
    (normalizedDensity_isStrictlyPositive P hP)

end InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit
