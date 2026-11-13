/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordColimitDimension
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Exact matrix representation at every native split-Clifford stage

The carrier here is the native Clifford quotient, not a matrix alias. The
existing recursive spinor representation is surjective at every stage; the
existing native dimension recurrence makes it injective. Coefficient extension
then retains one copy of an arbitrary real algebra, without assuming that its
elements commute or that its real dimension is finite.

The binary index order is precisely `SpinorRep.tensorIndexEquivFinPowTwo`:
the recursive Clifford head occupies the rightmost matrix tensor index.
Changing this order requires an explicit matrix reindexing.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Module

namespace InfoGeometry.Clifford.SplitCliffordMatrixEquiv

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordColimitDimension
open InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep

/-- Include the empty native Clifford stage in the existing dimension law. -/
theorem splitClNNAlg_finrank (n : ℕ) :
    Module.finrank ℝ (SplitClNNAlg n) = 4 ^ n := by
  cases n with
  | zero =>
      have h := splitClNNAlg_finrank_succ 0
      rw [show 0 + 1 = 1 from rfl, splitClNNAlg_finrank_one] at h
      norm_num only [pow_zero]
      omega
  | succ n => exact splitClNNAlg_finrank_succStage n

/-- Finiteness is derived from the positive dimension, not supplied as input. -/
theorem splitClNNAlg_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SplitClNNAlg n) := by
  apply Module.finite_of_finrank_pos
  rw [splitClNNAlg_finrank]
  positivity

theorem spinorMatrix_finrank_all (n : ℕ) :
    Module.finrank ℝ (SpinorMatrix n) = 4 ^ n := by
  simp only [SpinorMatrix, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one]
  rw [← mul_pow]
  norm_num

/-- Faithfulness of the actual recursively constructed Clifford representation. -/
theorem spinorRepresentation_bijective (n : ℕ) :
    Function.Bijective (spinorRepresentation n) := by
  letI := splitClNNAlg_finiteDimensional n
  have hdim : Module.finrank ℝ (Cl_split n) =
      Module.finrank ℝ (SpinorMatrix n) := by
    rw [spinorMatrix_finrank_all]
    exact splitClNNAlg_finrank n
  have hsurj : Function.Surjective (spinorRepresentation n).toLinearMap :=
    splitSpinorRepresentation_surjective_of_gammaTensor n
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj,
    hsurj⟩

/-- Native `Cl(n,n)`, for every `n`, with the existing recursive generator map. -/
def splitSpinorAlgEquiv (n : ℕ) : Cl_split n ≃ₐ[ℝ] SpinorMatrix n :=
  AlgEquiv.ofBijective (spinorRepresentation n) (spinorRepresentation_bijective n)

@[simp] theorem splitSpinorAlgEquiv_apply (n : ℕ) (x : Cl_split n) :
    splitSpinorAlgEquiv n x = spinorRepresentation n x := rfl

@[simp] theorem splitSpinorAlgEquiv_ι (n : ℕ) (v : SplitSpace n) :
    splitSpinorAlgEquiv n (CliffordAlgebra.ι (SplitQuad n) v) =
      recursiveGamma n v := spinorRepresentation_ι n v

universe u
variable (B : Type u) [Ring B] [Algebra ℝ B]

/-- The coefficient algebra occurs once, after the native Clifford stage.
The tensor flip is Mathlib's algebra equivalence and does not reverse the
order of products inside `B`. -/
def coefficientMatrixEquiv (n : ℕ) :
    (Cl_split n ⊗[ℝ] B) ≃ₐ[ℝ]
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B :=
  (Algebra.TensorProduct.congr (splitSpinorAlgEquiv n) (AlgEquiv.refl : B ≃ₐ[ℝ] B)).trans
    ((Algebra.TensorProduct.comm ℝ (SpinorMatrix n) B).trans
      (matrixEquivTensor (Fin (2 ^ n)) ℝ B).symm)

/-- Readback of a simple tensor; real matrix entries are central coefficients. -/
theorem coefficientMatrixEquiv_tmul (n : ℕ) (x : Cl_split n) (b : B) :
    coefficientMatrixEquiv B n (x ⊗ₜ[ℝ] b) =
      b • (spinorRepresentation n x).map (algebraMap ℝ B) := by
  simp [coefficientMatrixEquiv]

/-- The inverse is defined on every matrix, including singular matrices. -/
def unroll (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B ≃ₐ[ℝ] (Cl_split n ⊗[ℝ] B) :=
  (coefficientMatrixEquiv B n).symm

@[simp] theorem reconstruct_unroll (n : ℕ)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) :
    coefficientMatrixEquiv B n (unroll B n M) = M :=
  (coefficientMatrixEquiv B n).apply_symm_apply M

@[simp] theorem unroll_reconstruct (n : ℕ) (x : Cl_split n ⊗[ℝ] B) :
    unroll B n (coefficientMatrixEquiv B n x) = x :=
  (coefficientMatrixEquiv B n).symm_apply_apply x

/-- Ordered operator products are retained by the inverse equivalence. -/
theorem unroll_mul (n : ℕ) (M N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) :
    unroll B n (M * N) = unroll B n M * unroll B n N :=
  map_mul (unroll B n) M N

/-- An explicit finite expansion of the inverse, with exactly one coefficient
from `B` in every term. -/
theorem unroll_expansion (n : ℕ)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) B) :
    unroll B n M =
      ∑ p : Fin (2 ^ n) × Fin (2 ^ n),
        (splitSpinorAlgEquiv n).symm (Matrix.single p.1 p.2 1) ⊗ₜ[ℝ] M p.1 p.2 := by
  apply (coefficientMatrixEquiv B n).injective
  simp only [reconstruct_unroll, map_sum, coefficientMatrixEquiv_tmul]
  simp only [← splitSpinorAlgEquiv_apply, AlgEquiv.apply_symm_apply]
  simpa [Matrix.map_single, Algebra.algebraMap_eq_smul_one, Fintype.sum_prod_type] using
    Matrix.matrix_eq_sum_single M

end InfoGeometry.Clifford.SplitCliffordMatrixEquiv
