/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSheetObservationalEntropy
import InfoGeometry.Quantum.ProjectiveCoarseGraining

/-!
# Two-sheet entropy for the native projective coarse-graining channel

This adapter specializes the existing complex-linear block-uniform channel
to the actual complementary family P and 1 - P. On positive inputs, the
complex trace coefficients are real and the channel agrees with the existing
two-sheet matrix used to evaluate the CFC logarithm and observational entropy.

The equality with that real-coefficient expression is not claimed for an
arbitrary complex input. The channel itself remains the full complex-linear
map from ProjectiveCoarseGraining. No commutation hypothesis is imposed on
the positive input and the projection.

The entropy and support statements below concern that actual channel.
Zero-probability sheets are included through the existing native support
factorization. Relative-entropy nonnegativity, equality rigidity, and time
monotonicity remain outside this adapter.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetProjectiveCoarseGraining

open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open PolarFrameTraceDensity MatrixEntropyUnitaryOrbit TwoSheetObservationalEntropy
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open InfoGeometry.Quantum.ProjectiveCoarseGraining

variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

/-- The two actual complementary projectors, with their original matrix carrier. -/
def binaryProjectors (P : Mat) : Fin 2 → Mat := ![P, 1 - P]

@[simp] theorem binaryProjectors_zero (P : Mat) : binaryProjectors P 0 = P := rfl

@[simp] theorem binaryProjectors_one (P : Mat) : binaryProjectors P 1 = 1 - P := rfl

theorem binaryProjectors_isStarProjection {P : Mat} (hP : IsStarProjection P) :
    ∀ i, IsStarProjection (binaryProjectors P i) := by
  intro i
  fin_cases i
  · exact hP
  · exact hP.one_sub

theorem binaryProjectors_sum (P : Mat) : ∑ i, binaryProjectors P i = 1 := by
  simp only [Fin.sum_univ_two, binaryProjectors_zero, binaryProjectors_one]
  abel

theorem binaryProjectors_orthogonal {P : Mat} (hP : IsStarProjection P) :
    ∀ i j, i ≠ j → binaryProjectors P i * binaryProjectors P j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact hP.mul_one_sub_self
  · exact hP.one_sub_mul_self
  · exact False.elim (hij rfl)

/-- Positivity makes the actual complex projector readout real. -/
theorem trace_projection_mul_eq_probability {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) :
    Matrix.trace (P * ρ) = (sheetProbability ρ P : ℂ) := by
  apply Complex.ext
  · change (Matrix.trace (P * ρ)).re = (Matrix.trace (ρ * P)).re
    exact congrArg Complex.re (Matrix.trace_mul_comm P ρ)
  · exact (Complex.nonneg_iff.mp (trace_projection_mul_nonneg P ρ hP hρ)).2.symm

theorem trace_projection_eq_traceMass {P : Mat} (hP : IsStarProjection P) :
    Matrix.trace P = (traceMass P : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hP.nonneg.posSemidef.trace_nonneg).2.symm

private theorem uniform_term_eq_real {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) :
    (Matrix.trace (P * ρ) / Matrix.trace P) • P =
      (sheetProbability ρ P / traceMass P) • P := by
  rw [trace_projection_mul_eq_probability hρ hP,
    trace_projection_eq_traceMass hP, ← Complex.ofReal_div]
  exact algebraMap_smul ℂ (sheetProbability ρ P / traceMass P) P

/-- The actual complex-linear channel agrees with the two-sheet CFC reference
on positive inputs. No positivity of either sheet probability is assumed. -/
theorem blockUniform_binary_eq_coarseGrainedState {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) :
    blockUniformChannel (binaryProjectors P) ρ = coarseGrainedState ρ P := by
  simp only [blockUniformChannel_apply, Fin.sum_univ_two,
    binaryProjectors_zero, binaryProjectors_one]
  rw [uniform_term_eq_real hρ hP, uniform_term_eq_real hρ hP.one_sub]
  rfl

/-- Density preservation is supplied by the existing general projective channel. -/
theorem blockUniform_binary_isDensity {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hρ1 : Matrix.trace ρ = 1) (hP : IsStarProjection P) :
    (blockUniformChannel (binaryProjectors P) ρ).PosSemidef ∧
      Matrix.trace (blockUniformChannel (binaryProjectors P) ρ) = 1 :=
  blockUniformChannel_is_density (binaryProjectors P)
    (binaryProjectors_isStarProjection hP) (binaryProjectors_sum P) ρ hρ hρ1

/-- Readout preservation remains an identity for all full complex inputs. -/
theorem blockUniform_binary_readout (ρ : Mat) {P : Mat} (hP : IsStarProjection P)
    (i : Fin 2) :
    Matrix.trace (binaryProjectors P i * blockUniformChannel (binaryProjectors P) ρ) =
      Matrix.trace (binaryProjectors P i * ρ) :=
  blockUniformChannel_readout (binaryProjectors P)
    (binaryProjectors_isStarProjection hP) (binaryProjectors_orthogonal hP) ρ i

/-- The true channel logarithm is evaluated by the existing native two-sheet CFC. -/
theorem neg_log_blockUniform_binary {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) :
    -CFC.log (blockUniformChannel (binaryProjectors P) ρ) =
      twoSheet P (-Real.log (sheetProbability ρ P / traceMass P))
        (-Real.log (sheetProbability ρ (1 - P) / traceMass (1 - P))) := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP, coarseGrainedState,
    neg_log_twoSheet hP]

/-- The channel's actual CFC cross-entropy equals the observational entropy. -/
theorem crossEntropy_blockUniform_binary {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    (Matrix.trace (ρ * (-CFC.log (blockUniformChannel (binaryProjectors P) ρ)))).re =
      observationalEntropy ρ P := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP]
  exact crossEntropy_eq_observationalEntropy ρ hP hP0 hP1

/-- Native matrix entropy of the actual projective channel output. -/
theorem matrixEntropy_blockUniform_binary {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    matrixEntropy (blockUniformChannel (binaryProjectors P) ρ) =
      observationalEntropy ρ P := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP]
  exact matrixEntropy_coarseGrainedState ρ hP hP0 hP1

/-- The exact entropy gap uses the existing ordered Umegaki kernel and the
actual complex-linear projective channel as its reference state. -/
theorem entropy_gap_blockUniform_binary {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    observationalEntropy ρ P - matrixEntropy ρ =
      (Matrix.trace (umegakiKernel ρ (blockUniformChannel (binaryProjectors P) ρ))).re := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP]
  exact entropy_gap_eq_umegakiKernel ρ hP hP0 hP1

theorem entropy_gap_blockUniform_binary_positiveTrace {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    observationalEntropy ρ P - matrixEntropy ρ =
      (umegakiRelativeEntropy (positiveTraceDensity (1 : Mat) zero_le_one)
        ρ (blockUniformChannel (binaryProjectors P) ρ)).re := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP]
  exact entropy_gap_eq_umegakiRelativeEntropy ρ hP hP0 hP1

/-- An explicit support factorization for the actual channel, including zero
sheet probabilities. This is not an inverse of the channel on all matrices. -/
theorem blockUniform_binary_support_factorization {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ρ * twoSheet P (traceMass P / sheetProbability ρ P)
        (traceMass (1 - P) / sheetProbability ρ (1 - P)) *
      blockUniformChannel (binaryProjectors P) ρ = ρ := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP]
  exact coarseGrainedState_support_factorization hρ hP hP0 hP1

/-- The actual channel reference contains the support of the positive input. -/
theorem blockUniform_binary_kernel_le {ρ P : Mat} (hρ : ρ.PosSemidef)
    (hP : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    LinearMap.ker (blockUniformChannel (binaryProjectors P) ρ).mulVecLin ≤
      LinearMap.ker ρ.mulVecLin := by
  rw [blockUniform_binary_eq_coarseGrainedState hρ hP]
  exact coarseGrainedState_kernel_le hρ hP hP0 hP1

end InfoGeometry.Canonical.TwoSheetProjectiveCoarseGraining
