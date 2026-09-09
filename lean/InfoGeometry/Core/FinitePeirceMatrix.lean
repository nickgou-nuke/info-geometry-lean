import InfoGeometry.Core.PeirceDecomposition
import Mathlib.RingTheory.Idempotents
import Mathlib.Data.Matrix.Basic

/-!
# Finite associative Peirce matrices with their corner constraints

The binary owner is generalized using Mathlib's actual complete orthogonal
idempotent predicate. A block array lives in `e i * A * e j`, not in an
unrestricted matrix algebra. Its unit is `diag e`, not the ambient matrix
identity. No primitive-idempotent or nonassociative Zorn claim is made.
-/

noncomputable section

namespace InfoGeometry.Core.FinitePeirceMatrix

open scoped BigOperators

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
variable [Fintype I] [DecidableEq I]

/-- The literal finite array of Peirce corners. -/
def blocks (e : I → A) (x : A) : Matrix I I A := fun i j => e i * x * e j

/-- Sum of the entries, with the operator order unchanged. -/
def assemble (B : Matrix I I A) : A := ∑ i, ∑ j, B i j

/-- Completeness reconstructs every operator, without any commutativity premise. -/
theorem assemble_blocks (e : I → A) (he : CompleteOrthogonalIdempotents e) (x : A) :
    assemble (blocks e x) = x := by
  simp only [assemble, blocks, ← Finset.mul_sum, ← Finset.sum_mul, he.complete,
    one_mul, mul_one]

/-- Matrix multiplication is exactly the Peirce composition law. -/
theorem blocks_mul (e : I → A) (he : CompleteOrthogonalIdempotents e) (x y : A) :
    blocks e (x * y) = blocks e x * blocks e y := by
  funext i j
  change e i * (x * y) * e j = ∑ k, (e i * x * e k) * (e k * y * e j)
  calc
    _ = e i * x * (∑ k, e k) * y * e j := by rw [he.complete]; simp [mul_assoc]
    _ = ∑ k, e i * x * e k * y * e j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have hk : e k * e k = e k := (he.idem k).eq
      calc
        e i * x * e k * y * e j = (e i * x) * (e k * e k) * (y * e j) := by
          rw [hk]
          simp only [mul_assoc]
        _ = (e i * x * e k) * (e k * y * e j) := by simp only [mul_assoc]

/-- The identity on corner arrays is the diagonal family of idempotents. -/
theorem blocks_one (e : I → A) (he : CompleteOrthogonalIdempotents e) :
    blocks e 1 = Matrix.diagonal e := by
  funext i j
  simp [blocks, he.toOrthogonalIdempotents.mul_eq, Matrix.diagonal]

/-- Wrong intermediate sectors annihilate. -/
theorem block_cross_zero (e : I → A) (he : OrthogonalIdempotents e)
    (x y : A) (i j k l : I) (hjk : j ≠ k) :
    blocks e x i j * blocks e y k l = 0 := by
  change (e i * x * e j) * (e k * y * e l) = 0
  calc
    _ = (e i * x) * (e j * e k) * (y * e l) := by simp only [mul_assoc]
    _ = 0 := by rw [he.ortho hjk]; simp

/-- Every individual off-diagonal corner is square-zero. -/
theorem off_diagonal_square_zero (e : I → A) (he : OrthogonalIdempotents e)
    (x : A) (i j : I) (hij : i ≠ j) :
    blocks e x i j * blocks e x i j = 0 :=
  block_cross_zero e he x x i j i j hij.symm

/-- Native linear subspace of arrays whose entries really belong to the corners. -/
def cornerSpace (e : I → A) : Submodule K (Matrix I I A) where
  carrier := {B | ∀ i j, e i * B i j * e j = B i j}
  zero_mem' := by simp
  add_mem' hB hC := by
    intro i j
    simp only [Matrix.add_apply, mul_add, add_mul, hB i j, hC i j]
  smul_mem' r B hB := by
    intro i j
    simpa only [Matrix.smul_apply, mul_smul_comm, smul_mul_assoc] using
      congrArg (r • ·) (hB i j)

/-- Cutting an operator yields a valid array of corners. -/
theorem blocks_mem (e : I → A) (he : OrthogonalIdempotents e) (x : A) :
    blocks e x ∈ cornerSpace (K := K) e := by
  intro i j
  change e i * (e i * x * e j) * e j = e i * x * e j
  calc
    _ = (e i * e i) * x * (e j * e j) := by simp only [mul_assoc]
    _ = _ := by rw [(he.idem i).eq, (he.idem j).eq]

/-- An arbitrary valid corner is fixed on its left and right separately. -/
theorem corner_left_right (e : I → A) (he : OrthogonalIdempotents e)
    (B : cornerSpace (K := K) e) (i j : I) :
    e i * B.1 i j = B.1 i j ∧ B.1 i j * e j = B.1 i j := by
  have hb := B.2 i j
  constructor
  · calc
      e i * B.1 i j = e i * (e i * B.1 i j * e j) := by rw [hb]
      _ = e i * B.1 i j * e j := by
        simp only [← mul_assoc, (he.idem i).eq]
      _ = B.1 i j := hb
  · calc
      B.1 i j * e j = (e i * B.1 i j * e j) * e j := by rw [hb]
      _ = e i * B.1 i j * e j := by
        rw [mul_assoc, (he.idem j).eq]
      _ = B.1 i j := hb

/-- Orthogonality isolates exactly one entry in a valid corner array. -/
theorem cut_corner (e : I → A) (he : OrthogonalIdempotents e)
    (B : cornerSpace (K := K) e) (i j k l : I) :
    e i * B.1 k l * e j = if i = k ∧ l = j then B.1 k l else 0 := by
  have hb := B.2 k l
  calc
    _ = (e i * e k) * B.1 k l * (e l * e j) := by
      conv_lhs => rw [← hb]
      simp only [mul_assoc]
    _ = _ := by
      by_cases hik : i = k
      · subst i
        by_cases hlj : l = j
        · subst j
          simpa [he.mul_eq] using B.2 k l
        · simp [he.mul_eq, hlj]
      · simp [he.mul_eq, hik]

/-- Reconstruction is two-sided on the constrained arrays. -/
theorem blocks_assemble (e : I → A) (he : OrthogonalIdempotents e)
    (B : cornerSpace (K := K) e) : blocks e (assemble B.1) = B.1 := by
  funext i j
  simp only [blocks, assemble, Finset.mul_sum, Finset.sum_mul]
  simp_rw [cut_corner e he B]
  have h : ∀ k l, (if i = k ∧ l = j then B.1 k l else 0) = if k = i then (if l = j then B.1 k l else 0) else 0 := by
    intro k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    · have hki : ¬(i = k) := fun h => hk h.symm
      simp [hk, hki]
  simp_rw [h]
  simp

/-- Complete Peirce data give an actual linear equivalence, not a law-field interface. -/
def cornerEquiv (e : I → A) (he : CompleteOrthogonalIdempotents e) :
    A ≃ₗ[K] cornerSpace (K := K) e where
  toFun x := ⟨blocks e x, blocks_mem e he.toOrthogonalIdempotents x⟩
  invFun B := assemble B.1
  left_inv := assemble_blocks e he
  right_inv B := Subtype.ext (blocks_assemble e he.toOrthogonalIdempotents B)
  map_add' x y := by
    apply Subtype.ext
    funext i j
    simp [blocks, mul_add, add_mul]
  map_smul' r x := by
    apply Subtype.ext
    funext i j
    simp [blocks, mul_smul_comm, smul_mul_assoc]

/-- The constrained matrix space is closed under the ordinary matrix product. -/
theorem cornerSpace_mul_mem (e : I → A) (he : CompleteOrthogonalIdempotents e)
    (B C : cornerSpace (K := K) e) : B.1 * C.1 ∈ cornerSpace (K := K) e := by
  have h : B.1 * C.1 = blocks e (assemble B.1 * assemble C.1) := by
    rw [blocks_mul e he, blocks_assemble e he.toOrthogonalIdempotents,
      blocks_assemble e he.toOrthogonalIdempotents]
  rw [h]
  exact blocks_mem e he.toOrthogonalIdempotents _

/-- Its left unit is the diagonal projector family, not the ambient matrix identity. -/
theorem corner_unit_left (e : I → A) (he : CompleteOrthogonalIdempotents e)
    (B : cornerSpace (K := K) e) : Matrix.diagonal e * B.1 = B.1 := by
  calc
    _ = blocks e 1 * blocks e (assemble B.1) := by
      rw [blocks_one e he, blocks_assemble e he.toOrthogonalIdempotents]
    _ = blocks e (1 * assemble B.1) := (blocks_mul e he _ _).symm
    _ = B.1 := by rw [one_mul, blocks_assemble e he.toOrthogonalIdempotents]

theorem corner_unit_right (e : I → A) (he : CompleteOrthogonalIdempotents e)
    (B : cornerSpace (K := K) e) : B.1 * Matrix.diagonal e = B.1 := by
  calc
    _ = blocks e (assemble B.1) * blocks e 1 := by
      rw [blocks_one e he, blocks_assemble e he.toOrthogonalIdempotents]
    _ = blocks e (assemble B.1 * 1) := (blocks_mul e he _ _).symm
    _ = B.1 := by rw [mul_one, blocks_assemble e he.toOrthogonalIdempotents]

/-- Uniqueness of the finite block decomposition. -/
theorem blocks_injective (e : I → A) (he : CompleteOrthogonalIdempotents e) :
    Function.Injective (blocks e) := by
  intro x y h
  have hs := congrArg assemble h
  simpa only [assemble_blocks e he] using hs

/-- Two-block specialization agrees with the pre-existing binary owner. -/
theorem binary_existing_components (p x : A) :
    blocks ![p, 1-p] x =
      !![PeirceDecomposition.component11 p x, PeirceDecomposition.component10 p x;
         PeirceDecomposition.component01 p x, PeirceDecomposition.component00 p x] := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

end InfoGeometry.Core.FinitePeirceMatrix
