/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ChiralBlockSpectralGap
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Concrete nonnormal and singular operator couplings

The abstract gap theorem applies to the full operator algebra on a nonzero
two-dimensional complex Hilbert space. The invertible coupling below does
not commute with its adjoint. Its inverse is supplied by an actual matrix
inverse and its chiral action has nonempty native spectrum with a positive
gap. A second, nonzero nilpotent coupling has an explicit zero mode, showing
why nonzero coupling alone cannot replace invertibility.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.BdGOperatorGeometryTests

open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.ChiralBlockSpectralGap
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open FiniteMatrix (FinKetSpace ketPi)
open CblinfunMatrix

abbrev TestSpace := FinKetSpace (Fin 2)
abbrev TestOperator := TestSpace →L[ℂ] TestSpace

def couplingMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]

def inverseMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 0, 1]

def coupling : TestOperator := matrixOp couplingMatrix

def inverseCoupling : TestOperator := matrixOp inverseMatrix

/-- The displayed inverse acts as a genuine right inverse on the Hilbert space. -/
theorem coupling_mul_inverse : coupling * inverseCoupling = 1 := by
  apply matrixOfOp_injective
  change matrixOfOp (coupling.comp inverseCoupling) =
    matrixOfOp (ContinuousLinearMap.id ℂ TestSpace)
  simp only [matrixOfOp_comp, coupling, inverseCoupling,
    matrixOfOp_matrixOp, matrixOfOp_id]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [couplingMatrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The same inverse is also a left inverse. -/
theorem inverse_mul_coupling : inverseCoupling * coupling = 1 := by
  apply matrixOfOp_injective
  change matrixOfOp (inverseCoupling.comp coupling) =
    matrixOfOp (ContinuousLinearMap.id ℂ TestSpace)
  simp only [matrixOfOp_comp, coupling, inverseCoupling,
    matrixOfOp_matrixOp, matrixOfOp_id]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [couplingMatrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Invertibility is witnessed by the actual matrix operator inverse. -/
theorem coupling_isUnit : IsUnit coupling := by
  exact ⟨⟨coupling, inverseCoupling, coupling_mul_inverse, inverse_mul_coupling⟩, rfl⟩

/-- This full matrix coupling is nonnormal: its two Gram operators differ. -/
theorem coupling_gram_ne : star coupling * coupling ≠ coupling * star coupling := by
  intro h
  have hentry := congrArg (fun T : TestOperator => matrixOfOp T 0 0) h
  change matrixOfOp ((star coupling).comp coupling) 0 0 =
    matrixOfOp (coupling.comp (star coupling)) 0 0 at hentry
  simp only [matrixOfOp_comp, ContinuousLinearMap.star_eq_adjoint,
    matrixOfOp_adjoint, coupling, matrixOfOp_matrixOp] at hentry
  norm_num [couplingMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The positive gap is a statement about a nonempty native operator spectrum. -/
theorem coupling_has_positive_spectral_gap :
    (spectrum ℂ (blockAction (diracOperator coupling))).Nonempty ∧
      ∃ m : ℝ, 0 < m ∧
        ∀ μ ∈ spectrum ℂ (blockAction (diracOperator coupling)), m ≤ ‖μ‖ := by
  exact ⟨spectrum.nonempty _,
    exists_positive_spectral_gap_of_isUnit coupling coupling_isUnit⟩

def nilpotentMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

def nilpotentCoupling : TestOperator := matrixOp nilpotentMatrix

/-- The singular example has nonzero intersector action. -/
theorem nilpotentCoupling_ne_zero : nilpotentCoupling ≠ 0 := by
  intro h
  have hentry := congrArg (fun T : TestOperator => matrixOfOp T 0 1) h
  norm_num [nilpotentCoupling, nilpotentMatrix] at hentry

/-- The singular coupling is genuinely nilpotent in the operator algebra. -/
theorem nilpotentCoupling_mul_self : nilpotentCoupling * nilpotentCoupling = 0 := by
  apply matrixOfOp_injective
  change matrixOfOp (nilpotentCoupling.comp nilpotentCoupling) = matrixOfOp 0
  simp only [matrixOfOp_comp, nilpotentCoupling, matrixOfOp_matrixOp, matrixOfOp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem ket_zero_ne_zero : (ketPi (0 : Fin 2) : TestSpace) ≠ 0 := by
  intro h
  have hentry := congrArg (fun v : TestSpace => v 0) h
  simp at hentry

/-- The first coordinate ket belongs to the actual coupling kernel. -/
theorem nilpotentCoupling_apply_ket_zero :
    nilpotentCoupling (ketPi (0 : Fin 2)) = 0 := by
  change FiniteMatrix.matrixOp nilpotentMatrix (ketPi (0 : Fin 2)) = 0
  ext i
  change (FiniteMatrix.matrixOp nilpotentMatrix (ketPi (0 : Fin 2)) : Fin 2 → ℂ) i = 0
  rw [FiniteMatrix.matrixOp_apply_ket]
  fin_cases i <;> rfl

def nilpotentZeroMode : TestSpace × TestSpace := (0, ketPi (0 : Fin 2))

theorem nilpotentZeroMode_ne_zero : nilpotentZeroMode ≠ 0 := by
  intro h
  exact ket_zero_ne_zero (congrArg Prod.snd h)

/-- The block operator has a native nonzero zero mode. -/
theorem nilpotentZeroMode_apply_eq_zero :
    blockAction (diracOperator nilpotentCoupling) nilpotentZeroMode = 0 := by
  rw [blockAction_dirac_apply]
  simp [nilpotentZeroMode, nilpotentCoupling_apply_ket_zero]

/-- The zero mode obstructs invertibility in the native bounded-operator algebra. -/
theorem nilpotent_blockAction_not_isUnit :
    ¬ IsUnit (blockAction (diracOperator nilpotentCoupling)) := by
  intro hunit
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  apply nilpotentZeroMode_ne_zero
  apply hinj
  simpa only [map_zero] using nilpotentZeroMode_apply_eq_zero

/-- Zero lies in the native spectrum of this nonzero-coupling block action. -/
theorem nilpotent_zero_mem_spectrum :
    (0 : ℂ) ∈ spectrum ℂ (blockAction (diracOperator nilpotentCoupling)) :=
  (spectrum.zero_mem_iff ℂ).mpr nilpotent_blockAction_not_isUnit

/-- A nonzero coupling alone does not imply a positive spectral gap. -/
theorem nilpotent_has_no_positive_spectral_gap :
    ¬ ∃ m : ℝ, 0 < m ∧
      ∀ μ ∈ spectrum ℂ (blockAction (diracOperator nilpotentCoupling)), m ≤ ‖μ‖ := by
  rintro ⟨m, hm, hgap⟩
  have hzero : m ≤ 0 := by simpa using hgap 0 nilpotent_zero_mem_spectrum
  exact hm.not_ge hzero

end InfoGeometry.OperatorAlgebra.BdGOperatorGeometryTests
