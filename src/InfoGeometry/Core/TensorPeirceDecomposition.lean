/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Finite tensor-Peirce block extraction for dyadic matrices

This file formalizes the recursive `2 × 2` block shape, its block
reassembly, the centralizer-homogenized extraction identities, and a ring
equivalence from flat dyadic matrices to a nested coefficient-matrix tower.
The equivalence is established by finite index reindexing and matrix
currying over a semiring, including noncommutative coefficient semirings. No
completed tensor product or analytic limit is asserted.
-/

universe u

namespace InfoGeometry.Core.TensorPeirceDecomposition

variable (R : Type u) [Semiring R]

/-- Recursive coefficient-ring tower with one binary matrix layer at each stage. -/
def TensorTower (R : Type u) : ℕ → Type u
  | 0 => R
  | n + 1 => Matrix (Fin 2) (Fin 2) (TensorTower R n)

@[instance_reducible] def tensorTowerSemiring : (n : ℕ) → Semiring (TensorTower R n)
  | 0 => inferInstanceAs (Semiring R)
  | n + 1 => by
      change Semiring (Matrix (Fin 2) (Fin 2) (TensorTower R n))
      letI := tensorTowerSemiring n
      exact inferInstance

instance (n : ℕ) : Semiring (TensorTower R n) := tensorTowerSemiring R n

/-- Standard-index matrix carrier at dyadic level `n`. -/
abbrev FlatMat (R : Type u) (n : ℕ) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R

/-- Upper matrix unit in the concrete two-dimensional finite-stage operator
carrier `FlatMat ℤ 1 = Matrix (Fin 2) (Fin 2) ℤ`. -/
def matrixUnit01 : FlatMat ℤ 1 := fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Lower matrix unit in the concrete two-dimensional finite-stage operator
carrier `FlatMat ℤ 1 = Matrix (Fin 2) (Fin 2) ℤ`. -/
def matrixUnit10 : FlatMat ℤ 1 := fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- The finite matrix carrier used by the tensor-Peirce construction is
genuinely noncommutative already at its first nontrivial dyadic stage. -/
theorem finite_stage_matrix_units_noncommute :
    matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
  intro h
  have h00 := congrArg (fun M : FlatMat ℤ 1 => M 0 0) h
  norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply,
    Fin.sum_univ_two] at h00

/-- Recursive binary tensor-coordinate index. Each successor adds one outer bit. -/
def PeirceIndex : ℕ → Type
  | 0 => Fin 1
  | n + 1 => Fin 2 × PeirceIndex n

instance (n : ℕ) : Fintype (PeirceIndex n) := by
  induction n with
  | zero => dsimp [PeirceIndex]; infer_instance
  | succ n ih => dsimp [PeirceIndex]; infer_instance

instance (n : ℕ) : DecidableEq (PeirceIndex n) := by
  induction n with
  | zero => dsimp [PeirceIndex]; infer_instance
  | succ n ih => dsimp [PeirceIndex]; infer_instance

/-- Direct computable matrix-currying ring equivalence
`Matrix α α (Matrix β β R) ≃+* Matrix (α × β) (α × β) R` over any semiring `R`. -/
def matrixCurryRingEquiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] :
    Matrix α α (Matrix β β R) ≃+* Matrix (α × β) (α × β) R where
  toFun A := Matrix.of fun i j => (A i.1 j.1) i.2 j.2
  invFun A := Matrix.of fun i j => Matrix.of fun k l => A (i, k) (j, l)
  left_inv A := by ext i j k l; rfl
  right_inv A := by ext i j; rfl
  map_mul' A B := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  map_add' A B := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rfl

/-- The recursively split coordinate space has the expected dyadic size. -/
theorem peirceIndex_card (n : ℕ) : Fintype.card (PeirceIndex n) = 2 ^ n := by
  induction n with
  | zero => simp [PeirceIndex]
  | succ n ih =>
      simp [PeirceIndex, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

/-- A chosen finite equivalence from recursive binary coordinates to `Fin (2^n)`. -/
noncomputable def peirceIndexEquivFin (n : ℕ) : PeirceIndex n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (peirceIndex_card n)

/-- The nested coefficient-matrix tower is ring-equivalent to matrices on its
recursive binary index. This is the precise finite-stage tensor-currying
statement; it does not identify the tower with a completed tensor product. -/
noncomputable def tensorTowerMatrixEquiv :
    (n : ℕ) → TensorTower R n ≃+* Matrix (PeirceIndex n) (PeirceIndex n) R
  | 0 => by
      exact {
        toFun := fun x _ _ => x
        invFun := fun M => M ⟨0, by omega⟩ ⟨0, by omega⟩
        left_inv := by intro x; rfl
        right_inv := by
          intro M
          ext i j
          fin_cases i
          fin_cases j
          rfl
        map_mul' := by
          intro x y
          ext i j
          fin_cases i
          fin_cases j
          change x * y = ∑ _k : Fin 1, x * y
          simp
        map_add' := by
          intro x y
          ext i j
          fin_cases i
          fin_cases j
          rfl }
  | n + 1 => by
      change Matrix (Fin 2) (Fin 2) (TensorTower R n) ≃+*
        Matrix (Fin 2 × PeirceIndex n) (Fin 2 × PeirceIndex n) R
      exact ((tensorTowerMatrixEquiv n).mapMatrix).trans
        (matrixCurryRingEquiv (R := R) (α := Fin 2) (β := PeirceIndex n))

/-- Reindexing gives a genuine ring equivalence for the recursive bit-indexed
matrix algebra, over any semiring. The target is matrices on the recursive
coordinate type, rather than a matrix whose coefficients are themselves
matrices. -/
noncomputable def flatMatIndexTowerEquiv (n : ℕ) :
    FlatMat R n ≃+* Matrix (PeirceIndex n) (PeirceIndex n) R :=
  (Matrix.reindexRingEquiv R (peirceIndexEquivFin n)).symm

/-- Reindexing that splits a dyadic matrix index into `(bit, remaining bits)`. -/
def dyadicIndexEquiv (n : ℕ) : Fin (2 ^ (n + 1)) ≃ Fin 2 × Fin (2 ^ n) := by
  have h : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
  exact ((finProdFinEquiv : Fin 2 × Fin (2 ^ n) ≃ Fin (2 * 2 ^ n)).trans
    (finCongr h)).symm

/-- One-step finite Peirce splitting `FlatMat R (n + 1) ≃+* Matrix (Fin 2) (Fin 2) (FlatMat R n)`. -/
def flatStepEquiv (n : ℕ) :
    FlatMat R (n + 1) ≃+* Matrix (Fin 2) (Fin 2) (FlatMat R n) :=
  (Matrix.reindexRingEquiv R (dyadicIndexEquiv n)).trans
    (matrixCurryRingEquiv (R := R) (α := Fin 2) (β := Fin (2 ^ n))).symm

/-- At level zero, a `1 × 1` matrix is isomorphic to its unique scalar entry in `R`. -/
def flatZeroEquiv : FlatMat R 0 ≃+* R where
  toFun A := A 0 0
  invFun r := fun _ _ => r
  left_inv A := by
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j]
  right_inv _ := rfl
  map_mul' A B := by simp [Matrix.mul_apply]
  map_add' _ _ := rfl

/-- **Full `n`-Stage Recursive Tensor-Peirce Ring Isomorphism (`peirceTowerEquiv`)**:
`Matrix (Fin (2^n)) (Fin (2^n)) R ≃+* TensorTower R n`. -/
def peirceTowerEquiv : (n : ℕ) → FlatMat R n ≃+* TensorTower R n
  | 0 => flatZeroEquiv (R := R)
  | n + 1 =>
      let step := flatStepEquiv (R := R) n
      let inner : Matrix (Fin 2) (Fin 2) (FlatMat R n) ≃+*
          Matrix (Fin 2) (Fin 2) (TensorTower R n) :=
        (peirceTowerEquiv n).mapMatrix
      step.trans inner

/-! ## Explicit Block Extractors, `toTensorTower` / `ofTensorTower`, and Centralizer Homogenization -/

/-- Canonical index splitting `Fin (2^n) ⊕ Fin (2^n) ≃ Fin (2^{n+1})`. -/
def finSplit (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  have h : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by ring
  finSumFinEquiv.trans (Fin.castOrderIso h).toEquiv

/-- Extracts the `(0,0)` upper-left `2^n × 2^n` Peirce block `P M P`. -/
def block00 {R : Type u} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inl i)) (finSplit n (Sum.inl j))

/-- Extracts the `(0,1)` upper-right `2^n × 2^n` Peirce block `P M (1 - P)`. -/
def block01 {R : Type u} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inl i)) (finSplit n (Sum.inr j))

/-- Extracts the `(1,0)` lower-left `2^n × 2^n` Peirce block `(1 - P) M P`. -/
def block10 {R : Type u} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inr i)) (finSplit n (Sum.inl j))

/-- Extracts the `(1,1)` lower-right `2^n × 2^n` Peirce block `(1 - P) M (1 - P)`. -/
def block11 {R : Type u} {n : ℕ} (M : FlatMat R (n + 1)) : FlatMat R n :=
  fun i j => M (finSplit n (Sum.inr i)) (finSplit n (Sum.inr j))

/-- Projects a `2^{n+1} × 2^{n+1}` matrix `M` into a `2 × 2` matrix of `2^n × 2^n` blocks:
`M ↦ ![![block00 M, block01 M], ![block10 M, block11 M]]`. -/
def peirceSplitStep {R : Type u} {n : ℕ} (M : FlatMat R (n + 1)) :
    Matrix (Fin 2) (Fin 2) (FlatMat R n) :=
  ![![block00 M, block01 M],
    ![block10 M, block11 M]]

/-- Inverse of `peirceSplitStep`: reassembles four `2^n × 2^n` blocks into a `2^{n+1} × 2^{n+1}` matrix. -/
def peirceUnsplitStep {R : Type u} {n : ℕ} (B : Matrix (Fin 2) (Fin 2) (FlatMat R n)) :
    FlatMat R (n + 1) :=
  Matrix.reindex (finSplit n) (finSplit n)
    (Matrix.fromBlocks (B 0 0) (B 0 1) (B 1 0) (B 1 1))

/-- Forward Tensor-Peirce Compiler (`toTensorTower`):
recursively decomposes a `2^n × 2^n` matrix into a nested `n`-level `TensorTower R n`. -/
def toTensorTower {R : Type u} : (n : ℕ) → FlatMat R n → TensorTower R n
  | 0,     M => M 0 0
  | n + 1, M =>
      let B := peirceSplitStep M
      ![![toTensorTower n (B 0 0), toTensorTower n (B 0 1)],
        ![toTensorTower n (B 1 0), toTensorTower n (B 1 1)]]

/-- Inverse Tensor-Peirce Coagulator (`ofTensorTower`):
recursively coagulates an `n`-level `TensorTower R n` back into a `2^n × 2^n` matrix. -/
def ofTensorTower {R : Type u} : (n : ℕ) → TensorTower R n → FlatMat R n
  | 0,     r => fun _ _ => r
  | n + 1, T =>
      peirceUnsplitStep
        ![![ofTensorTower n (T 0 0), ofTensorTower n (T 0 1)],
          ![ofTensorTower n (T 1 0), ofTensorTower n (T 1 1)]]

theorem peirceSplitStep_peirceUnsplitStep {R : Type u} {n : ℕ}
    (B : Matrix (Fin 2) (Fin 2) (FlatMat R n)) :
    peirceSplitStep (peirceUnsplitStep B) = B := by
  ext a b i j
  fin_cases a <;> fin_cases b <;>
    simp [peirceSplitStep, block00, block01, block10, block11,
      peirceUnsplitStep, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem peirceUnsplitStep_peirceSplitStep {R : Type u} {n : ℕ}
    (M : FlatMat R (n + 1)) :
    peirceUnsplitStep (peirceSplitStep M) = M := by
  ext i j
  have hi := (finSplit n).apply_symm_apply i
  have hj := (finSplit n).apply_symm_apply j
  rw [← hi, ← hj]
  cases hri : (finSplit n).symm i with
  | inl i' =>
      cases hrj : (finSplit n).symm j with
      | inl j' => simp [peirceUnsplitStep, peirceSplitStep, block00,
          Matrix.reindex_apply, Matrix.fromBlocks]
      | inr j' => simp [peirceUnsplitStep, peirceSplitStep, block01,
          Matrix.reindex_apply, Matrix.fromBlocks]
  | inr i' =>
      cases hrj : (finSplit n).symm j with
      | inl j' => simp [peirceUnsplitStep, peirceSplitStep, block10,
          Matrix.reindex_apply, Matrix.fromBlocks]
      | inr j' => simp [peirceUnsplitStep, peirceSplitStep, block11,
          Matrix.reindex_apply, Matrix.fromBlocks]

theorem toTensorTower_ofTensorTower {R : Type u} :
    ∀ (n : ℕ) (T : TensorTower R n), toTensorTower n (ofTensorTower n T) = T
  | 0,     _ => rfl
  | n + 1, T => by
      dsimp [toTensorTower, ofTensorTower]
      have hB := peirceSplitStep_peirceUnsplitStep
        (R := R) (n := n)
        ![![ofTensorTower n (T 0 0), ofTensorTower n (T 0 1)],
          ![ofTensorTower n (T 1 0), ofTensorTower n (T 1 1)]]
      rw [hB]
      apply Matrix.ext
      intro a b
      fin_cases a <;> fin_cases b <;> simp [toTensorTower_ofTensorTower n]

theorem ofTensorTower_toTensorTower {R : Type u} :
    ∀ (n : ℕ) (M : FlatMat R n), ofTensorTower n (toTensorTower n M) = M
  | 0, M => by
      ext i j
      fin_cases i
      fin_cases j
      rfl
  | n + 1, M => by
      change peirceUnsplitStep
        (![![ofTensorTower n (toTensorTower n (peirceSplitStep M 0 0)),
            ofTensorTower n (toTensorTower n (peirceSplitStep M 0 1))],
          ![ofTensorTower n (toTensorTower n (peirceSplitStep M 1 0)),
            ofTensorTower n (toTensorTower n (peirceSplitStep M 1 1))]]) = M
      have hblocks :
          ![![ofTensorTower n (toTensorTower n (peirceSplitStep M 0 0)),
              ofTensorTower n (toTensorTower n (peirceSplitStep M 0 1))],
            ![ofTensorTower n (toTensorTower n (peirceSplitStep M 1 0)),
              ofTensorTower n (toTensorTower n (peirceSplitStep M 1 1))]] =
            peirceSplitStep M := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [ofTensorTower_toTensorTower n, peirceSplitStep]
      rw [hblocks, peirceUnsplitStep_peirceSplitStep]

section AlgebraicPeirceHomogenization

variable {B : Type*} [Ring B]

/-- Homogenized `(0,0)` Tensor-Peirce projection `π₀₀(M) := E₀₀ M E₀₀ + E₁₀ M E₀₁`. -/
def pi00 (E00 E01 E10 _E11 M : B) : B := E00 * M * E00 + E10 * M * E01

/-- Homogenized `(0,1)` Tensor-Peirce projection `π₀₁(M) := E₀₀ M E₁₀ + E₁₀ M E₁₁`. -/
def pi01 (E00 _E01 E10 E11 M : B) : B := E00 * M * E10 + E10 * M * E11

/-- Homogenized `(1,0)` Tensor-Peirce projection `π₁₀(M) := E₀₁ M E₀₀ + E₁₁ M E₀₁`. -/
def pi10 (E00 E01 _E10 E11 M : B) : B := E01 * M * E00 + E11 * M * E01

/-- Homogenized `(1,1)` Tensor-Peirce projection `π₁₁(M) := E₀₁ M E₁₀ + E₁₁ M E₁₁`. -/
def pi11 (_E00 E01 E10 E11 M : B) : B := E01 * M * E10 + E11 * M * E11

/-- Universal exact reconstruction `M = E₀₀ π₀₀(M) + E₀₁ π₀₁(M) + E₁₀ π₁₀(M) + E₁₁ π₁₁(M)`. -/
theorem tensor_peirce_exact_reconstruction
    (E00 E01 E10 E11 M : B)
    (h_sum : E00 + E11 = 1)
    (h00_00 : E00 * E00 = E00) (h00_10 : E00 * E10 = 0)
    (h01_00 : E01 * E00 = 0)   (h01_10 : E01 * E10 = E00)
    (h10_01 : E10 * E01 = E11) (h10_11 : E10 * E11 = 0)
    (h11_01 : E11 * E01 = 0)   (h11_11 : E11 * E11 = E11) :
    E00 * pi00 E00 E01 E10 E11 M +
    E01 * pi01 E00 E01 E10 E11 M +
    E10 * pi10 E00 E01 E10 E11 M +
    E11 * pi11 E00 E01 E10 E11 M = M := by
  unfold pi00 pi01 pi10 pi11
  simp only [mul_add, ← mul_assoc,
             h00_00, h00_10, h01_00, h01_10, h10_01, h10_11, h11_01, h11_11,
             zero_mul, add_zero, zero_add]
  calc E00 * M * E00 + E00 * M * E11 + E11 * M * E00 + E11 * M * E11
    _ = (E00 + E11) * M * (E00 + E11) := by
        noncomm_ring
    _ = 1 * M * 1 := by rw [h_sum]
    _ = M := by rw [one_mul, mul_one]

/-- Block-matrix `(0,0)` outer unit `[[1, 0], [0, 0]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE00 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 1 0 0 0

/-- Block-matrix `(0,1)` outer shift unit `[[0, 1], [0, 0]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE01 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 1 0 0

/-- Block-matrix `(1,0)` outer shift unit `[[0, 0], [1, 0]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE10 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 1 0

/-- Block-matrix `(1,1)` outer unit `[[0, 0], [0, 1]]` on `Matrix (m ⊕ m) (m ⊕ m) R`. -/
def blkE11 {m R : Type*} [DecidableEq m] [Zero R] [One R] : Matrix (m ⊕ m) (m ⊕ m) R :=
  Matrix.fromBlocks 0 0 0 1

/-- **Theorem (`fromBlocks_pi_homogenization`)**:
On any `2 × 2` block matrix `Matrix.fromBlocks M00 M01 M10 M11 : Matrix (m ⊕ m) (m ⊕ m) R`,
the four centralizer-homogenized Tensor-Peirce projections `pi00`, `pi01`, `pi10`, `pi11`
extract each block `M_{ab}` into the diagonal commutant `Matrix.fromBlocks M_{ab} 0 0 M_{ab} = I_2 ⊗ M_{ab}`. -/
theorem fromBlocks_pi_homogenization
    {m R : Type*} [Fintype m] [DecidableEq m] [Ring R]
    (M00 M01 M10 M11 : Matrix m m R) :
    pi00 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M00 0 0 M00 ∧
    pi01 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M01 0 0 M01 ∧
    pi10 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M10 0 0 M10 ∧
    pi11 blkE00 blkE01 blkE10 blkE11 (Matrix.fromBlocks M00 M01 M10 M11) =
      Matrix.fromBlocks M11 0 0 M11 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [pi00, pi01, pi10, pi11, blkE00, blkE01, blkE10, blkE11,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

end AlgebraicPeirceHomogenization

end InfoGeometry.Core.TensorPeirceDecomposition
