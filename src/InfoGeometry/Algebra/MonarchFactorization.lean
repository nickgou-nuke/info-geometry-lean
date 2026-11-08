/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ordered two-stage routing on a product index

The first stage mixes fine indices within a fixed coarse index. The second
mixes coarse indices within a fixed fine index. Both stages are native block
diagonal matrices, with a product-index exchange for the first stage.

The product has a rank-one slice when the fine output and coarse input are
fixed. This is not the ordinary block obtained by fixing both coarse indices.
A rational four-state example distinguishes the two slices and proves that
this factorization class is not closed under squaring.

The results concern exact finite matrix operations. They do not assert
universality, an operation-count bound, or a GPU implementation refinement.
-/

noncomputable section

namespace InfoGeometry.Algebra.MonarchFactorization

open scoped BigOperators Matrix

section General

variable {I J 𝕜 : Type*}

/-- Fix the fine output and coarse input; vary the coarse output and fine input. -/
def routingSlice (M : Matrix (I × J) (I × J) 𝕜) (a : J) (j : I) :
    Matrix I J 𝕜 :=
  M.submatrix (fun i => (i, a)) (fun b => (j, b))

section Zero

variable [Zero 𝕜] [DecidableEq I] [DecidableEq J]

/-- Coarse mixing preserves the fine index. -/
def coarseMix (L : J → Matrix I I 𝕜) : Matrix (I × J) (I × J) 𝕜 :=
  Matrix.blockDiagonal L

/-- Fine mixing preserves the coarse index, after exchanging the product indices. -/
def fineMix (R : I → Matrix J J 𝕜) : Matrix (I × J) (I × J) 𝕜 :=
  Matrix.reindex (Equiv.prodComm J I) (Equiv.prodComm J I) (Matrix.blockDiagonal R)

omit [DecidableEq I] in
@[simp] theorem coarseMix_apply (L : J → Matrix I I 𝕜) (i j : I) (a b : J) :
    coarseMix L (i, a) (j, b) = if a = b then L a i j else 0 := rfl

omit [DecidableEq J] in
@[simp] theorem fineMix_apply (R : I → Matrix J J 𝕜) (i j : I) (a b : J) :
    fineMix R (i, a) (j, b) = if i = j then R i a b else 0 := rfl

end Zero

section Semiring

variable [Semiring 𝕜] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Fine mixing acts first on column vectors; coarse mixing acts second. -/
def monarch (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜) :
    Matrix (I × J) (I × J) 𝕜 :=
  coarseMix L * fineMix R

/-- The factorization class is the image of the two actual block-mixing stages. -/
def IsMonarch (M : Matrix (I × J) (I × J) 𝕜) : Prop :=
  ∃ (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜), M = monarch L R

/-- The sole intermediate index contributing to this product is `(j,a)`. -/
@[simp] theorem monarch_apply (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜)
    (i j : I) (a b : J) :
    monarch L R (i, a) (j, b) = L a i j * R j a b := by
  simp only [monarch, Matrix.mul_apply, Fintype.sum_prod_type,
    coarseMix_apply, fineMix_apply]
  simp [ite_mul, mul_ite]

omit [DecidableEq J] in
/-- The first stage is an independent fine-index matrix-vector product per coarse index. -/
theorem fineMix_mulVec (R : I → Matrix J J 𝕜) (x : I × J → 𝕜)
    (j : I) (a : J) :
    (fineMix R *ᵥ x) (j, a) = ∑ b : J, R j a b * x (j, b) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

omit [DecidableEq I] in
/-- The second stage is an independent coarse-index matrix-vector product per fine index. -/
theorem coarseMix_mulVec (L : J → Matrix I I 𝕜) (x : I × J → 𝕜)
    (i : I) (a : J) :
    (coarseMix L *ᵥ x) (i, a) = ∑ j : I, L a i j * x (j, a) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

/-- Exact two-stage execution, with the order of scalar factors retained. -/
theorem monarch_mulVec (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜)
    (x : I × J → 𝕜) (i : I) (a : J) :
    (monarch L R *ᵥ x) (i, a) =
      ∑ j : I, L a i j * (∑ b : J, R j a b * x (j, b)) := by
  rw [monarch, ← Matrix.mulVec_mulVec, coarseMix_mulVec]
  simp only [fineMix_mulVec]

/-- The rank restriction applies to this crossed-index slice. -/
theorem routingSlice_monarch (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜)
    (a : J) (j : I) :
    routingSlice (monarch L R) a j =
      Matrix.vecMulVec (fun i => L a i j) (fun b => R j a b) := by
  ext i b
  exact monarch_apply L R i j a b

end Semiring

section Rank

variable [Field 𝕜] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Mathlib's native matrix rank of every routing slice is at most one. -/
theorem routingSlice_monarch_rank_le_one
    (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜) (a : J) (j : I) :
    (routingSlice (monarch L R) a j).rank ≤ 1 := by
  rw [routingSlice_monarch]
  exact Matrix.rank_vecMulVec_le _ _

end Rank

section Minors

variable [CommRing 𝕜] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Every two-by-two minor of a routing slice vanishes. -/
theorem routingSlice_monarch_minor_eq_zero
    (L : J → Matrix I I 𝕜) (R : I → Matrix J J 𝕜)
    (a : J) (j i₁ i₂ : I) (b₁ b₂ : J) :
    routingSlice (monarch L R) a j i₁ b₁ * routingSlice (monarch L R) a j i₂ b₂ -
      routingSlice (monarch L R) a j i₁ b₂ * routingSlice (monarch L R) a j i₂ b₁ = 0 := by
  have scalarMinor : ∀ w x y z : 𝕜, (w * x) * (y * z) - (w * z) * (y * x) = 0 := by
    intro w x y z
    ring
  simpa only [routingSlice_monarch, Matrix.vecMulVec_apply] using
    scalarMinor (L a i₁ j) (R j a b₁) (L a i₂ j) (R j a b₂)

/-- A nonzero crossed-index minor obstructs every possible two-stage factorization. -/
theorem IsMonarch.routingSlice_minor_eq_zero
    {M : Matrix (I × J) (I × J) 𝕜} (hM : IsMonarch M)
    (a : J) (j i₁ i₂ : I) (b₁ b₂ : J) :
    routingSlice M a j i₁ b₁ * routingSlice M a j i₂ b₂ -
      routingSlice M a j i₁ b₂ * routingSlice M a j i₂ b₁ = 0 := by
  obtain ⟨L, R, rfl⟩ := hM
  exact routingSlice_monarch_minor_eq_zero L R a j i₁ i₂ b₁ b₂

end Minors

end General

namespace FourStateWitness

/-- The actual coarse block used in both fine sectors of the witness. -/
def coarseBlock : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 1, 1]

/-- The actual fine swap used in the second coarse sector. -/
def fineSwap : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

/-- The concrete coefficient blocks themselves retain a nonzero order obstruction. -/
theorem coarseBlock_fineSwap_noncommute : ¬ Commute coarseBlock fineSwap := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 0) h.eq
  norm_num [coarseBlock, fineSwap, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- A lower triangular coarse block, identical at both fine indices. -/
def leftBlocks (_ : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ := coarseBlock

/-- The first coarse sector retains the fine index; the second swaps it. -/
def rightBlocks (j : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ :=
  if j = 0 then 1 else fineSwap

/-- In ordinary coarse blocks this is `[[I,0],[I,X]]`. -/
def witness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ :=
  monarch leftBlocks rightBlocks

theorem witness_isMonarch : IsMonarch witness :=
  ⟨leftBlocks, rightBlocks, rfl⟩

/-- An ordinary coarse block can be the full two-dimensional identity. -/
theorem witness_ordinaryBlock_eq_one :
    witness.submatrix (fun a => ((0 : Fin 2), a)) (fun b => ((0 : Fin 2), b)) =
      (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext a b
  simp [witness, leftBlocks, rightBlocks, coarseBlock]

/-- The claimed rank-one restriction on ordinary coarse blocks is false. -/
theorem witness_ordinaryBlock_rank_two :
    (witness.submatrix (fun a => ((0 : Fin 2), a))
      (fun b => ((0 : Fin 2), b))).rank = 2 := by
  rw [witness_ordinaryBlock_eq_one, Matrix.rank_one]
  simp

/-- Squaring creates a crossed-index slice with a nonzero determinant. -/
theorem witness_square_routingSlice :
    routingSlice (witness * witness) 0 0 =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i b
  simp only [routingSlice, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases b <;>
    norm_num [witness, leftBlocks, rightBlocks, coarseBlock, fineSwap]

theorem witness_square_minor_eq_one :
    routingSlice (witness * witness) 0 0 0 0 *
        routingSlice (witness * witness) 0 0 1 1 -
      routingSlice (witness * witness) 0 0 0 1 *
        routingSlice (witness * witness) 0 0 1 0 = (1 : ℚ) := by
  rw [witness_square_routingSlice]
  norm_num

/-- This particular square admits no Monarch factorization, for any block parameters. -/
theorem witness_square_not_isMonarch : ¬ IsMonarch (witness * witness) := by
  intro hM
  have hminor := hM.routingSlice_minor_eq_zero 0 0 0 1 0 1
  rw [witness_square_minor_eq_one] at hminor
  norm_num at hminor

/-- Nonclosure is an existential obstruction, not a statement about every square. -/
theorem exists_monarch_square_not_isMonarch :
    ∃ M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℚ,
      IsMonarch M ∧ ¬ IsMonarch (M * M) :=
  ⟨witness, witness_isMonarch, witness_square_not_isMonarch⟩

end FourStateWitness

end InfoGeometry.Algebra.MonarchFactorization
