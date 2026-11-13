/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact rank-sized factorization of a finite matrix

A basis of the actual range of `M.mulVecLin` gives a factorization through
`Fin M.rank`. The multiplication-rank inequality proves that this is the
least possible inner dimension. The zero matrix uses the empty inner index
`Fin 0`; no positivity assumption on bond dimensions is imposed.

Applied to one tensor unfolding, this proves optimality at that cut. It does
not yet construct one compatible train attaining every unfolding rank.
-/

namespace InfoGeometry.Algebra.MatrixRankFactorization

open scoped BigOperators Kronecker

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

/-- Choose coordinates on the native linear-map range, then factor the
matrix as its range inclusion times its range-restricted map. The inclusion
has an actual left inverse, including when the range is zero-dimensional. -/
theorem exists_rank_factorization_with_left_inverse (M : Matrix m n K) :
    ∃ L : Matrix m (Fin M.rank) K,
      ∃ R : Matrix (Fin M.rank) n K,
        ∃ Q : Matrix (Fin M.rank) m K, L * R = M ∧ Q * L = 1 := by
  classical
  let b : Module.Basis (Fin M.rank) K (LinearMap.range M.mulVecLin) :=
    Module.finBasis K (LinearMap.range M.mulVecLin)
  obtain ⟨q, hq⟩ :=
    (LinearMap.range M.mulVecLin).subtype.exists_leftInverse_of_injective
      (Submodule.ker_subtype _)
  refine ⟨
    LinearMap.toMatrix b (Pi.basisFun K m) (LinearMap.range M.mulVecLin).subtype,
    LinearMap.toMatrix (Pi.basisFun K n) b M.mulVecLin.rangeRestrict,
    LinearMap.toMatrix (Pi.basisFun K m) b q,
    ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_rangeRestrict]
    simpa only [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] using
      (LinearMap.toMatrix_toLin (Pi.basisFun K n) (Pi.basisFun K m) M)
  · rw [← LinearMap.toMatrix_comp, hq, LinearMap.toMatrix_id]

/-- Exact rectangular factorization through `Fin M.rank`. -/
theorem exists_rank_factorization (M : Matrix m n K) :
    ∃ L : Matrix m (Fin M.rank) K,
      ∃ R : Matrix (Fin M.rank) n K, L * R = M := by
  obtain ⟨L, R, Q, hLR, _⟩ := exists_rank_factorization_with_left_inverse M
  exact ⟨L, R, hLR⟩

/-- Native matrix rank is exactly the least inner dimension of an exact
two-factor decomposition, including inner dimension zero. -/
theorem rank_isLeast_factor_width (M : Matrix m n K) :
    IsLeast {r : ℕ | ∃ L : Matrix m (Fin r) K,
      ∃ R : Matrix (Fin r) n K, L * R = M} M.rank := by
  refine ⟨exists_rank_factorization M, ?_⟩
  rintro r ⟨L, R, hLR⟩
  calc
    M.rank = (L * R).rank := congrArg Matrix.rank hLR.symm
    _ ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ r := by simpa using Matrix.rank_le_card_width L

/-- A matrix has rank at most one exactly when it is one outer product.
The zero matrix is included; rank exactly one would require nonzeroness. -/
theorem rank_le_one_iff_vecMulVec (M : Matrix m n K) :
    M.rank ≤ 1 ↔ ∃ u : m → K, ∃ v : n → K, Matrix.vecMulVec u v = M := by
  constructor
  · intro h
    have hf := exists_rank_factorization M
    by_cases hzero : M.rank = 0
    · rw [hzero] at hf
      obtain ⟨L, R, hLR⟩ := hf
      have hM : M = 0 := by
        ext i j
        rw [← hLR, Matrix.mul_apply]
        simp
      refine ⟨0, 0, ?_⟩
      rw [hM]
      ext i j
      simp [Matrix.vecMulVec]
    · have hone : M.rank = 1 :=
        Nat.le_antisymm h (Nat.one_le_iff_ne_zero.mpr hzero)
      rw [hone] at hf
      obtain ⟨L, R, hLR⟩ := hf
      refine ⟨fun i => L i 0, fun j => R 0 j, ?_⟩
      ext i j
      simpa [Matrix.mul_apply, Matrix.vecMulVec] using
        congrArg (fun A : Matrix m n K => A i j) hLR
  · rintro ⟨u, v, rfl⟩
    exact Matrix.rank_vecMulVec_le u v

/-- Entrywise form of the native outer-product criterion. -/
theorem rank_le_one_iff_pure (M : Matrix m n K) :
    M.rank ≤ 1 ↔ ∃ u : m → K, ∃ v : n → K, ∀ i j, M i j = u i * v j := by
  rw [rank_le_one_iff_vecMulVec]
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨u, v, ?_⟩
    intro i j
    exact (congrArg (fun A : Matrix m n K => A i j) h).symm
  · rintro ⟨u, v, h⟩
    refine ⟨u, v, ?_⟩
    ext i j
    exact (h i j).symm

/-- One nonzero two-by-two minor obstructs every single pure coefficient
factorization. This criterion needs no custom tensor-rank definition. -/
theorem not_pure_of_cross_mul_ne (M : Matrix m n K) (i j : m) (k l : n)
    (hminor : M i k * M j l ≠ M i l * M j k) :
    ¬ ∃ u : m → K, ∃ v : n → K, ∀ a b, M a b = u a * v b := by
  rintro ⟨u, v, h⟩
  apply hminor
  rw [h i k, h j l, h i l, h j k]
  ring

/-- The signed-half coefficient minor occurring in the controlled-`K`
example, with rows `(I, η)` and columns `(I, K)` in the intake convention. -/
def signedHalfMinor (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => if i = 1 ∧ j = 1 then -(1 / 2 : K) else (1 / 2 : K)

theorem signedHalfMinor_det [CharZero K] :
    (signedHalfMinor K).det = -(1 / 2 : K) := by
  norm_num [signedHalfMinor, Matrix.det_fin_two]

theorem signedHalfMinor_rank [CharZero K] : (signedHalfMinor K).rank = 2 := by
  have hdet : (signedHalfMinor K).det ≠ 0 := by
    rw [signedHalfMinor_det]
    norm_num
  simpa using Matrix.rank_of_det_ne_zero hdet

theorem signedHalfMinor_not_pure [CharZero K] :
    ¬ ∃ u : Fin 2 → K, ∃ v : Fin 2 → K,
      ∀ i j, signedHalfMinor K i j = u i * v j := by
  apply not_pure_of_cross_mul_ne (signedHalfMinor K) 0 1 0 1
  norm_num [signedHalfMinor]

section Reshape

/-- Moving one physical index from the column side to the row side commutes
with left multiplication through a Kronecker lift. The coefficient order is
unchanged, so this coordinate identity holds over a noncommutative semiring. -/
theorem reshape_mul_eq_kronecker_mul
    {B a b c s : Type*} [Semiring B] [Fintype s] [Fintype b] [DecidableEq b]
    (L : Matrix a s B) (R : Matrix s (b × c) B) :
    (Matrix.of fun ab z => (L * R) ab.1 (ab.2, z) : Matrix (a × b) c B) =
      (L ⊗ₖ (1 : Matrix b b B)) *
        (Matrix.of fun sb z => R sb.1 (sb.2, z) : Matrix (s × b) c B) := by
  ext ab z
  rcases ab with ⟨i, j⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, ite_mul]

/-- A proved left inverse makes the reshape step rank-preserving. This is
the algebraic step required by successive minimal-rank tensor factorizations. -/
theorem rank_reshape_mul_of_left_inverse
    {a b c s : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype s]
    [DecidableEq s] (L : Matrix a s K) (Q : Matrix s a K)
    (hQL : Q * L = 1) (R : Matrix s (b × c) K) :
    (Matrix.of fun ab z => (L * R) ab.1 (ab.2, z) : Matrix (a × b) c K).rank =
      (Matrix.of fun sb z => R sb.1 (sb.2, z) : Matrix (s × b) c K).rank := by
  classical
  let T : Matrix (s × b) c K := Matrix.of fun sb z => R sb.1 (sb.2, z)
  have hLift : (Q ⊗ₖ (1 : Matrix b b K)) * (L ⊗ₖ (1 : Matrix b b K)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hQL, Matrix.one_mul, Matrix.one_kronecker_one]
  have hRecover : (Q ⊗ₖ (1 : Matrix b b K)) *
      ((L ⊗ₖ (1 : Matrix b b K)) * T) = T := by
    rw [← Matrix.mul_assoc, hLift, Matrix.one_mul]
  rw [reshape_mul_eq_kronecker_mul]
  change ((L ⊗ₖ (1 : Matrix b b K)) * T).rank = T.rank
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc
    T.rank = ((Q ⊗ₖ (1 : Matrix b b K)) *
        ((L ⊗ₖ (1 : Matrix b b K)) * T)).rank :=
      congrArg Matrix.rank hRecover.symm
    _ ≤ ((L ⊗ₖ (1 : Matrix b b K)) * T).rank := Matrix.rank_mul_le_right _ _

end Reshape

end InfoGeometry.Algebra.MatrixRankFactorization
