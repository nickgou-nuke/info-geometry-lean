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

/-- The inverse of `matrixEquivCliffordTensor`, identifying `Clsplit k ⊗[ℝ] A` with
`M_{2^k}(A)` while preserving an arbitrary (possibly noncommutative) coefficient `ℝ`-algebra `A`. -/
def cliffordTensorEquivMatrix (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    Clsplit k ⊗[ℝ] A ≃ₐ[ℝ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) A :=
  (matrixEquivCliffordTensor k A).symm

@[simp]
theorem cliffordTensorEquivMatrix_symm (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    (cliffordTensorEquivMatrix k A).symm = matrixEquivCliffordTensor k A :=
  rfl

theorem matrixEquivCliffordTensor_symm (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    (matrixEquivCliffordTensor k A).symm = cliffordTensorEquivMatrix k A :=
  rfl

/-- Explicit action of `cliffordTensorEquivMatrix` on pure tensors. -/
theorem cliffordTensorEquivMatrix_tmul (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A]
    (x : Clsplit k) (a : A) :
    cliffordTensorEquivMatrix k A (x ⊗ₜ[ℝ] a) =
      a • (splitTowerEquivMatrix k x).map (algebraMap ℝ A) := by
  simp [cliffordTensorEquivMatrix, matrixEquivCliffordTensor,
    Algebra.TensorProduct.comm_symm_tmul, Algebra.TensorProduct.congr_symm_apply,
    matrixEquivTensor_apply_symm]

/-- Coefficient-algebra preservation: `1 ⊗ₜ[ℝ] a` maps to the scalar matrix `a • I`. -/
@[simp]
theorem cliffordTensorEquivMatrix_one_tmul (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a : A) :
    cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) = Matrix.scalar (Fin (2 ^ k)) a := by
  rw [cliffordTensorEquivMatrix_tmul, map_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem cliffordTensorEquivMatrix_one_tmul_eq_diagonal
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a : A) :
    cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) = Matrix.diagonal (fun _ => a) := by
  rw [cliffordTensorEquivMatrix_one_tmul, Matrix.scalar_apply]

/-- Composing `cliffordTensorEquivMatrix` with the right tensor inclusion yields
`Matrix.scalarAlgHom`. -/
theorem cliffordTensorEquivMatrix_comp_includeRight
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    (cliffordTensorEquivMatrix k A).toAlgHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[ℝ] Clsplit k ⊗[ℝ] A) =
      Matrix.scalarAlgHom (Fin (2 ^ k)) ℝ := by
  ext1 a
  simp [Algebra.TensorProduct.includeRight_apply]

@[simp]
theorem matrixEquivCliffordTensor_scalar
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a : A) :
    matrixEquivCliffordTensor k A (Matrix.scalar (Fin (2 ^ k)) a) = (1 : Clsplit k) ⊗ₜ[ℝ] a := by
  simpa [cliffordTensorEquivMatrix] using
    congrArg (matrixEquivCliffordTensor k A) (cliffordTensorEquivMatrix_one_tmul k A a).symm

@[simp]
theorem cliffordTensorEquivMatrix_tmul_one
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (x : Clsplit k) :
    cliffordTensorEquivMatrix k A (x ⊗ₜ[ℝ] (1 : A)) =
      (splitTowerEquivMatrix k x).map (algebraMap ℝ A) := by
  rw [cliffordTensorEquivMatrix_tmul, one_smul]

/-- Elements of the Clifford factor commute with elements of the coefficient algebra factor. -/
theorem tmul_one_commute_one_tmul
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (x : Clsplit k) (a : A) :
    Commute (x ⊗ₜ[ℝ] (1 : A)) ((1 : Clsplit k) ⊗ₜ[ℝ] a) := by
  change (x ⊗ₜ[ℝ] (1 : A)) * ((1 : Clsplit k) ⊗ₜ[ℝ] a) =
    ((1 : Clsplit k) ⊗ₜ[ℝ] a) * (x ⊗ₜ[ℝ] (1 : A))
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem includeLeft_commute_includeRight
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (x : Clsplit k) (a : A) :
    Commute (Algebra.TensorProduct.includeLeft (R := ℝ) (S := ℝ) (A := Clsplit k) (B := A) x)
      (Algebra.TensorProduct.includeRight a) := by
  simpa [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] using
    tmul_one_commute_one_tmul k A x a

theorem map_splitTower_commute_scalar
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (x : Clsplit k) (a : A) :
    Commute ((splitTowerEquivMatrix k x).map (algebraMap ℝ A)) (Matrix.scalar (Fin (2 ^ k)) a) := by
  have h := (tmul_one_commute_one_tmul k A x a).map (cliffordTensorEquivMatrix k A).toAlgHom
  simpa using h

/-- The embedding `a ↦ 1 ⊗ₜ[ℝ] a` of the coefficient algebra is injective without extra
assumptions. -/
theorem includeRight_injective (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[ℝ] Clsplit k ⊗[ℝ] A) := by
  intro a b h
  have : Nonempty (Fin (2 ^ k)) := ⟨⟨0, pow_pos (by decide) k⟩⟩
  have hmat := congrArg (cliffordTensorEquivMatrix k A) h
  simp only [Algebra.TensorProduct.includeRight_apply, cliffordTensorEquivMatrix_one_tmul] at hmat
  exact Matrix.scalar_inj.mp hmat

@[simp]
theorem one_tmul_inj (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] {a b : A} :
    (1 : Clsplit k) ⊗ₜ[ℝ] a = (1 : Clsplit k) ⊗ₜ[ℝ] b ↔ a = b :=
  (includeRight_injective k A).eq_iff

@[simp]
theorem includeRight_commute_iff (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a b : A) :
    Commute ((1 : Clsplit k) ⊗ₜ[ℝ] a) ((1 : Clsplit k) ⊗ₜ[ℝ] b) ↔ Commute a b := by
  change ((1 : Clsplit k) ⊗ₜ[ℝ] a) * ((1 : Clsplit k) ⊗ₜ[ℝ] b) =
      ((1 : Clsplit k) ⊗ₜ[ℝ] b) * ((1 : Clsplit k) ⊗ₜ[ℝ] a) ↔ a * b = b * a
  simp [Algebra.TensorProduct.tmul_mul_tmul, one_tmul_inj]

theorem includeRight_not_commute_iff (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a b : A) :
    ((1 : Clsplit k) ⊗ₜ[ℝ] a) * ((1 : Clsplit k) ⊗ₜ[ℝ] b) ≠
      ((1 : Clsplit k) ⊗ₜ[ℝ] b) * ((1 : Clsplit k) ⊗ₜ[ℝ] a) ↔ a * b ≠ b * a :=
  not_congr (includeRight_commute_iff k A a b)

theorem cliffordTensorEquivMatrix_one_tmul_commute_iff
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a b : A) :
    Commute (cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a))
      (cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] b)) ↔ Commute a b := by
  change cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) *
        cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] b) =
      cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] b) *
        cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) ↔ Commute a b
  rw [← map_mul, ← map_mul, (cliffordTensorEquivMatrix k A).injective.eq_iff]
  exact includeRight_commute_iff k A a b

theorem cliffordTensorEquivMatrix_one_tmul_not_commute_iff
    (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] (a b : A) :
    cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) *
        cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] b) ≠
      cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] b) *
        cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) ↔ a * b ≠ b * a :=
  not_congr (cliffordTensorEquivMatrix_one_tmul_commute_iff k A a b)

/-- When `A` is nontrivial, the left Clifford factor `x ↦ x ⊗ₜ[ℝ] 1` also embeds injectively. -/
theorem includeLeft_injective (k : ℕ) (A : Type*) [Ring A] [Algebra ℝ A] [Nontrivial A] :
    Function.Injective (Algebra.TensorProduct.includeLeft : Clsplit k →ₐ[ℝ] Clsplit k ⊗[ℝ] A) := by
  intro x y h
  have hmat := congrArg (cliffordTensorEquivMatrix k A) h
  simp only [Algebra.TensorProduct.includeLeft_apply, cliffordTensorEquivMatrix_tmul_one] at hmat
  have hinj : Function.Injective (algebraMap ℝ A) := RingHom.injective (algebraMap ℝ A)
  have hsplit : splitTowerEquivMatrix k x = splitTowerEquivMatrix k y := by
    ext i j
    exact hinj (congrArg (fun M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) A => M i j) hmat)
  exact (splitTowerEquivMatrix k).injective hsplit

end

end InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
