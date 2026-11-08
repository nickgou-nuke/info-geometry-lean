/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Analysis.OperatorDirichletScaling
import InfoGeometry.Canonical.PolarFrameTraceDensity
import InfoGeometry.OperatorAlgebra.TracialGNSDirichlet
import Mathlib.Tactic.NormNum

/-! # A full matrix GNS operator with both a vacuum and a positive eigenvalue

The two input matrices are the existing noncommuting, self-adjoint swap and
tilted matrices. On the actual completed GNS space of the ordinary matrix
trace, their commutator is a nonzero eigenvector of the constructed Dirichlet
operator with eigenvalue nine. The identity remains a zero mode. No
finite-dimensionality instance for the GNS completion is assumed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TracialGNSMatrixTests

open InfoGeometry.Algebra.MatrixNoncommutativity
open InfoGeometry.Analysis.OperatorDirichletLaplacian
open InfoGeometry.Canonical.PolarFrameTraceDensity
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- The ordinary trace as an actual positive linear functional on the full matrix algebra. -/
def matrixTrace : Mat →ₚ[ℂ] ℂ := positiveTraceDensity 1 (by positivity)

@[simp] theorem matrixTrace_apply (a : Mat) : matrixTrace a = Matrix.trace a := by
  simp [matrixTrace]

theorem matrixTrace_tracial (a b : Mat) : matrixTrace (a * b) = matrixTrace (b * a) := by
  simpa using Matrix.trace_mul_comm a b

theorem matrixTrace_faithful (a : Mat) (ha : matrixTrace (star a * a) = 0) : a = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  simpa only [matrixTrace_apply, Matrix.star_eq_conjTranspose] using ha

theorem matrixTrace_one : matrixTrace 1 = 2 := by
  norm_num [Matrix.trace, Fin.sum_univ_two]

def inputs : Fin 2 → Mat := ![swapMatrix, tiltedMatrix]

theorem inputs_isSelfAdjoint (i : Fin 2) : IsSelfAdjoint (inputs i) := by
  fin_cases i <;> change star _ = _ <;> simp [inputs]

theorem inputs_not_commute : ¬ Commute (inputs 0) (inputs 1) := by
  intro h
  exact swapMatrix_mul_tiltedMatrix_ne h.eq

def commutatorMatrix : Mat := swapMatrix * tiltedMatrix - tiltedMatrix * swapMatrix

theorem commutatorMatrix_eq : commutatorMatrix = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commutatorMatrix, swapMatrix, tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem commutatorMatrix_ne_zero : commutatorMatrix ≠ 0 :=
  sub_ne_zero.mpr swapMatrix_mul_tiltedMatrix_ne

/-- The two double commutators are checked in the complete matrix algebra. -/
theorem swap_double_commutator :
    (swapMatrix : Mat) * (swapMatrix * commutatorMatrix - commutatorMatrix * swapMatrix) -
      (swapMatrix * commutatorMatrix - commutatorMatrix * swapMatrix) * swapMatrix =
        (4 : ℂ) • commutatorMatrix := by
  rw [commutatorMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem tilted_double_commutator :
    (tiltedMatrix : Mat) *
        (tiltedMatrix * commutatorMatrix - commutatorMatrix * tiltedMatrix) -
      (tiltedMatrix * commutatorMatrix - commutatorMatrix * tiltedMatrix) * tiltedMatrix =
        (5 : ℂ) • commutatorMatrix := by
  rw [commutatorMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tiltedMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def commutatorFamily (i : Fin 2) : matrixTrace.GNS →L[ℂ] matrixTrace.GNS :=
  matrixTrace.tracialCommutatorGNS matrixTrace_tracial (inputs i)

def matrixLaplacian : matrixTrace.GNS →L[ℂ] matrixTrace.GNS :=
  matrixTrace.tracialDirichletGNS matrixTrace_tracial inputs

def commutatorVector : matrixTrace.GNS := matrixTrace.toPreGNS commutatorMatrix

theorem commutatorVector_ne_zero : commutatorVector ≠ 0 := by
  exact (matrixTrace.toPreGNS_coe_eq_zero_iff_of_faithful
    matrixTrace_faithful commutatorMatrix).not.mpr commutatorMatrix_ne_zero

theorem adjoint_commutatorFamily (i : Fin 2) :
    ContinuousLinearMap.adjoint (commutatorFamily i) = commutatorFamily i := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact (matrixTrace.tracialCommutatorGNS_selfAdjoint matrixTrace_tracial
    (inputs i) (inputs_isSelfAdjoint i)).star_eq

/-- The concrete matrix identity becomes an eigenvector equation on the native GNS completion. -/
theorem matrixLaplacian_commutatorVector :
    matrixLaplacian commutatorVector = (9 : ℂ) • commutatorVector := by
  change laplacian commutatorFamily commutatorVector = _
  simp only [laplacian, Fin.sum_univ_two, add_apply,
    ContinuousLinearMap.comp_apply, adjoint_commutatorFamily]
  change matrixTrace.tracialCommutatorGNS matrixTrace_tracial swapMatrix
      (matrixTrace.tracialCommutatorGNS matrixTrace_tracial swapMatrix
        (matrixTrace.toPreGNS commutatorMatrix : matrixTrace.GNS)) +
    matrixTrace.tracialCommutatorGNS matrixTrace_tracial tiltedMatrix
      (matrixTrace.tracialCommutatorGNS matrixTrace_tracial tiltedMatrix
        (matrixTrace.toPreGNS commutatorMatrix : matrixTrace.GNS)) = _
  simp only [PositiveLinearMap.tracialCommutatorGNS_toPreGNS,
    swap_double_commutator, tilted_double_commutator, map_smul,
    UniformSpace.Completion.coe_smul]
  rw [← add_smul]
  norm_num [commutatorVector]

theorem zero_mem_spectrum_matrixLaplacian : (0 : ℂ) ∈ spectrum ℂ matrixLaplacian := by
  apply matrixTrace.zero_mem_spectrum_tracialDirichletGNS matrixTrace_tracial _ inputs
  rw [matrixTrace_one]
  norm_num

/-- The positive part of the spectrum is nonempty; no finite-dimensionality premise is used. -/
theorem nine_mem_spectrum_matrixLaplacian : (9 : ℂ) ∈ spectrum ℂ matrixLaplacian := by
  rw [ContinuousLinearMap.spectrum_eq]
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := commutatorVector)
  exact ⟨Module.End.mem_eigenspace_iff.mpr matrixLaplacian_commutatorVector,
    commutatorVector_ne_zero⟩

theorem commutatorVector_mem_kernelOrthogonal :
    commutatorVector ∈ kernelOrthogonal commutatorFamily :=
  eigenvector_mem_kernelOrthogonal commutatorFamily (by norm_num : (9 : ℂ) ≠ 0)
    matrixLaplacian_commutatorVector

/-- The complement on which a gap is sought is demonstrably nonzero. -/
theorem kernelOrthogonal_has_nonzero :
    ∃ x : matrixTrace.GNS, x ∈ kernelOrthogonal commutatorFamily ∧ x ≠ 0 :=
  ⟨commutatorVector, commutatorVector_mem_kernelOrthogonal, commutatorVector_ne_zero⟩

/-- Even this fixed noncommuting matrix family has no lower bound uniform over all positive scales. -/
theorem no_uniform_positive_scaling_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ kernelOrthogonal (fun i => r • commutatorFamily i),
        c * ‖x‖ ^ 2 ≤ energy (fun i => r • commutatorFamily i) x :=
  not_exists_uniform_positive_coercive_bound commutatorFamily kernelOrthogonal_has_nonzero

end InfoGeometry.OperatorAlgebra.TracialGNSMatrixTests
