/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11GradedTensorUntwist
import InfoGeometry.Clifford.Tower
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Matrix classification of the existing split Clifford tower

The carrier and quadratic forms are exactly `CliffordTower.SplitSpace` and
`CliffordTower.Qsplit`. The native one-step untwisting is iterated, with native
matrix composition and finite-index reindexing, to construct the real algebra
equivalence `Clsplit n ≃ₐ[ℝ] Matrix (Fin (2^n)) (Fin (2^n)) ℝ`.

Extending the matrix scalars to an arbitrary real algebra `A` gives
`M_(2^n)(A) ≃ₐ[ℝ] Clsplit n ⊗[ℝ] A`. The coefficient algebra need not commute.
-/

namespace InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv

open InfoGeometry.CliffordTower
open Cl11GradedTensorUntwist
open scoped TensorProduct

noncomputable section

/-- Untwisting on the already-defined successor quadratic form. -/
def splitTowerStep (n : ℕ) :
    Clsplit (n + 1) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (Clsplit n) := by
  change CliffordAlgebra (InfoGeometry.Clifford.splitQ11.prod (Qsplit n)) ≃ₐ[ℝ] _
  rw [← Cl11Matrix.q11_eq_splitQ11]
  exact splitCliffordEquivMatrix (Qsplit n)

private def zeroSpaceIsometry :
    (Qsplit 0).IsometryEquiv (0 : QuadraticForm ℝ Unit) where
  toLinearEquiv := LinearEquiv.ofSubsingleton _ _
  map_app' v := by simp [Qsplit]

/-- The zero-stage Clifford algebra is its scalar ring. -/
def splitZeroEquivScalars : Clsplit 0 ≃ₐ[ℝ] ℝ :=
  (CliffordAlgebra.equivOfIsometry zeroSpaceIsometry).trans CliffordAlgebraRing.equiv

private def doubledIndexEquiv (n : ℕ) :
    Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  Fintype.equivFinOfCardEq (by simp [pow_succ, Nat.mul_comm])

/-- An actual algebra isomorphism for every stage of the existing split tower. -/
def splitTowerEquivMatrix : (n : ℕ) →
    Clsplit n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  Nat.rec
    (motive := fun n => Clsplit n ≃ₐ[ℝ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ)
    (by
      letI : Fintype Unit := Unique.fintype
      letI : DecidableEq Unit := fun a b => decidableEq_of_subsingleton a b
      exact (splitZeroEquivScalars.trans
        (Matrix.uniqueAlgEquiv (R := ℝ) (A := ℝ) (m := Unit)).symm).trans
          (Matrix.reindexAlgEquiv ℝ ℝ (Equiv.ofUnique Unit (Fin 1))))
    (fun n prev =>
      (splitTowerStep n).trans
        (prev.mapMatrix.trans
          ((Matrix.compAlgEquiv (Fin 2) (Fin (2 ^ n)) ℝ ℝ).trans
            (Matrix.reindexAlgEquiv ℝ ℝ (doubledIndexEquiv n)))))

/-- Scalar extension keeps the entire, potentially noncommutative,
coefficient algebra as a tensor factor. -/
def matrixEquivCliffordTensor (n : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) A ≃ₐ[ℝ] Clsplit n ⊗[ℝ] A :=
  (matrixEquivTensor (Fin (2 ^ n)) ℝ A).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[ℝ] A)
      (splitTowerEquivMatrix n).symm).trans (Algebra.TensorProduct.comm ℝ A (Clsplit n)))

end

end InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
