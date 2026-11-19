/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PolarFrameTraceDensity
import InfoGeometry.Canonical.QuantumRelativeSurprisal
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
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

/-- The full noncommutative Umegaki relative-entropy readout is invariant under
unitary conjugation of both strictly positive matrix arguments.  The proof
uses the CFC logarithm naturality and the positive functional induced by the
matrix trace; no simultaneous diagonalization or commutation hypothesis is
used. -/
theorem umegakiRelativeEntropy_unitary_conjugate
    (U : unitary Mat) (ρ σ : Mat)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
        (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ =
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
        (Matrix.tracePositiveLinearMap n ℂ ℂ)
        ((U : Mat) * ρ * star (U : Mat))
        ((U : Mat) * σ * star (U : Mat)) := by
  let φ := Unitary.conjStarAlgAut ℂ Mat U
  let τ := Matrix.tracePositiveLinearMap n ℂ ℂ
  have hτ : ∀ X : Mat, τ (φ X) = τ X := by
    intro X
    simp [τ, φ, Matrix.tracePositiveLinearMap_apply,
      Unitary.conjStarAlgAut_apply, trace_unitary_conjugate]
  have hlog : ∀ P : Mat, IsStrictlyPositive P →
      ContinuousOn Real.log (spectrum ℝ P) := by
    intro P hP
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hP.spectrum_pos hx)
  exact InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy_starAlgHom_eq
    φ.toStarAlgHom τ τ hτ ρ σ hρ.isSelfAdjoint hσ.isSelfAdjoint
    (hlog ρ hρ) (hlog σ hσ)

private lemma complex_convex_sub (t : ℝ) (a x y : ℂ) :
    (t : ℂ) * (a - x) + ((1 - t : ℝ) : ℂ) * (a - y) =
      a - ((t : ℂ) * x + ((1 - t : ℝ) : ℂ) * y) := by
  push_cast
  ring

/-- For fixed faithful `ρ`, the full noncommutative Umegaki trace readout is
convex in its second argument.  This is a finite-matrix consequence of CFC
operator concavity of `log`; no commuting or diagonalization hypothesis is
used. -/
theorem umegakiRelativeEntropy_convex_second_argument
    (ρ σ₁ σ₂ : Mat) (t : ℝ)
    (hρ : IsStrictlyPositive ρ) (hσ₁ : IsStrictlyPositive σ₁)
    (hσ₂ : IsStrictlyPositive σ₂) (ht : 0 < t) (ht' : t < 1) :
    InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
        (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ (t • σ₁ + (1 - t) • σ₂) ≤
      (t : ℂ) *
          InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
            (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ₁ +
        ((1 - t : ℝ) : ℂ) *
          InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
            (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ₂ := by
  let τ := Matrix.tracePositiveLinearMap n ℂ ℂ
  have hlog := positiveTraceDensity_log_jensen ρ σ₁ σ₂ t hρ.nonneg
    hσ₁ hσ₂ ht ht'
  have hform (σ : Mat) :
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
          τ ρ σ =
        positiveTraceDensity ρ hρ.nonneg (CFC.log ρ - CFC.log σ) := by
    simp [τ, InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy,
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel,
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.relativeLogDensity,
      Matrix.tracePositiveLinearMap_apply, positiveTraceDensity_apply, CFC.log]
  rw [hform, hform, hform]
  let A := positiveTraceDensity ρ hρ.nonneg (CFC.log ρ)
  let L₁ := positiveTraceDensity ρ hρ.nonneg (CFC.log σ₁)
  let L₂ := positiveTraceDensity ρ hρ.nonneg (CFC.log σ₂)
  let Lm := positiveTraceDensity ρ hρ.nonneg (CFC.log (t • σ₁ + (1 - t) • σ₂))
  have hsub (σ : Mat) :
      positiveTraceDensity ρ hρ.nonneg (CFC.log ρ - CFC.log σ) =
        positiveTraceDensity ρ hρ.nonneg (CFC.log ρ) -
          positiveTraceDensity ρ hρ.nonneg (CFC.log σ) := by
    rw [map_sub]
  have hneg : -Lm ≤ -((t : ℂ) * L₁ + ((1 - t : ℝ) : ℂ) * L₂) := by
    dsimp [Lm, L₁, L₂]
    exact neg_le_neg hlog
  have horder : A - Lm ≤ A - ((t : ℂ) * L₁ + ((1 - t : ℝ) : ℂ) * L₂) := by
    have hadd := add_le_add_left hneg A
    dsimp [A, Lm, L₁, L₂] at hadd ⊢
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  have hcombine :
      (t : ℂ) * (A - L₁) + ((1 - t : ℝ) : ℂ) * (A - L₂) =
        A - ((t : ℂ) * L₁ + ((1 - t : ℝ) : ℂ) * L₂) :=
    complex_convex_sub t A L₁ L₂
  rw [hsub (t • σ₁ + (1 - t) • σ₂), hsub σ₁, hsub σ₂]
  change A - Lm ≤
    (t : ℂ) * (A - L₁) + ((1 - t : ℝ) : ℂ) * (A - L₂)
  calc
    A - Lm ≤ A - ((t : ℂ) * L₁ + ((1 - t : ℝ) : ℂ) * L₂) := horder
    _ = (t : ℂ) * (A - L₁) + ((1 - t : ℝ) : ℂ) * (A - L₂) := hcombine.symm

/-- For fixed strictly positive `ρ`, increasing the reference operator in
Loewner order decreases the full noncommutative Umegaki trace readout. -/
theorem umegakiRelativeEntropy_antitone_reference
    (ρ σ₁ σ₂ : Mat)
    (hρ : IsStrictlyPositive ρ) (hσ₁ : IsStrictlyPositive σ₁)
    (hσ : σ₁ ≤ σ₂) :
    InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
        (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ₂ ≤
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
        (Matrix.tracePositiveLinearMap n ℂ ℂ) ρ σ₁ := by
  let τ := Matrix.tracePositiveLinearMap n ℂ ℂ
  have hlog := positiveTraceDensity_log_monotone ρ σ₁ σ₂ hρ.nonneg hσ₁ hσ
  have hform (σ : Mat) :
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
          τ ρ σ =
        positiveTraceDensity ρ hρ.nonneg (CFC.log ρ - CFC.log σ) := by
    simp [τ, InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy,
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel,
      InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.relativeLogDensity,
      Matrix.tracePositiveLinearMap_apply, positiveTraceDensity_apply, CFC.log]
  rw [hform σ₂, hform σ₁]
  have hneg :
      -positiveTraceDensity ρ hρ.nonneg (CFC.log σ₂) ≤
        -positiveTraceDensity ρ hρ.nonneg (CFC.log σ₁) := neg_le_neg hlog
  have horder :
      positiveTraceDensity ρ hρ.nonneg (CFC.log ρ) -
          positiveTraceDensity ρ hρ.nonneg (CFC.log σ₂) ≤
        positiveTraceDensity ρ hρ.nonneg (CFC.log ρ) -
          positiveTraceDensity ρ hρ.nonneg (CFC.log σ₁) := by
    have hadd := add_le_add_left hneg
      (positiveTraceDensity ρ hρ.nonneg (CFC.log ρ))
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  have hsub (σ : Mat) :
      positiveTraceDensity ρ hρ.nonneg (CFC.log ρ - CFC.log σ) =
        positiveTraceDensity ρ hρ.nonneg (CFC.log ρ) -
          positiveTraceDensity ρ hρ.nonneg (CFC.log σ) := by
    rw [map_sub]
  rw [hsub σ₂, hsub σ₁]
  exact horder

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
