import Mathlib
import InfoGeometry.Canonical.CountProbabilityState
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# InfoGeometry.Canonical.FiniteKetMatrixCountBridge

Pointwise finite ket/matrix substrate for AFP-style executable operator
semantics and count-vector lifts.

This file keeps the first layer deliberately finite and function-native:

* kets are point masses `Pi.single i 1`,
* finite operators are matrices acting on finite function spaces,
* count vectors are pointwise functions before projectivization,
* projective count geometry is delegated to the existing `PositiveRayCore` owner.

The purpose is to make the AFP-to-Lean bridge explicit before lifting the same
operators into the Hestenes/Krein/modular lanes.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteKetMatrixCountBridge

open InfoGeometry.Canonical.PositiveRayCore

universe u v w

/-- Finite ket space: pointwise complex functions on a finite index type. -/
@[rep_depth operator]
abbrev FinKetSpace (ι : Type u) := ι → ℂ

/-- Basis ket `|i⟩`, represented as the point mass at `i`. -/
@[rep_depth operator]
def ketPi {ι : Type u} [DecidableEq ι] (i : ι) : FinKetSpace ι :=
  Pi.single i (1 : ℂ)

@[simp, rep_depth operator]
theorem ketPi_apply_same {ι : Type u} [DecidableEq ι] (i : ι) :
    ketPi i i = 1 := by
  simp [ketPi]

@[simp, rep_depth operator]
theorem ketPi_apply_ne {ι : Type u} [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    ketPi i j = 0 := by
  simp [ketPi, h]

section MatrixOperators

variable {ι : Type u} {κ : Type v} {τ : Type w}
variable [Fintype ι] [Fintype κ] [Fintype τ]

/--
Finite matrix as a continuous linear operator on pointwise finite ket spaces.

The coefficient convention is `A k i`, sending input index `i` to output index `k`.
-/
@[rep_depth operator]
def matrixOp (A : Matrix κ ι ℂ) : FinKetSpace ι →L[ℂ] FinKetSpace κ where
  toFun x := fun k => ∑ i : ι, A k i * x i
  map_add' x y := by
    ext k
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext k
    simp [mul_assoc, Finset.mul_sum]
  cont := by
    fun_prop

@[simp, rep_depth operator]
theorem matrixOp_apply (A : Matrix κ ι ℂ) (x : FinKetSpace ι) (k : κ) :
    matrixOp A x k = ∑ i : ι, A k i * x i :=
  rfl

/-- Matrix entries are recovered by applying the operator to a basis ket. -/
@[simp, rep_depth operator]
theorem matrixOp_apply_ket [DecidableEq ι]
    (A : Matrix κ ι ℂ) (i : ι) (k : κ) :
    matrixOp A (ketPi i) k = A k i := by
  classical
  simpa [matrixOp, ketPi, Matrix.dotProduct] using
    (Matrix.dotProduct_single_one (v := fun j : ι => A k j) i)

/-- Operator extensionality on finite ket spaces is pointwise extensionality. -/
@[rep_depth operator]
theorem matrixOp_ext_pointwise
    {T U : FinKetSpace ι →L[ℂ] FinKetSpace κ}
    (h : ∀ x k, T x k = U x k) :
    T = U := by
  ext x k
  exact h x k

@[simp, rep_depth operator]
theorem matrixOp_zero :
    matrixOp (0 : Matrix κ ι ℂ) = 0 := by
  ext x k
  simp [matrixOp]

@[simp, rep_depth operator]
theorem matrixOp_add (A B : Matrix κ ι ℂ) :
    matrixOp (A + B) = matrixOp A + matrixOp B := by
  ext x k
  simp [matrixOp, add_mul, Finset.sum_add_distrib]

@[simp, rep_depth operator]
theorem matrixOp_smul (c : ℂ) (A : Matrix κ ι ℂ) :
    matrixOp (c • A) = c • matrixOp A := by
  ext x k
  simp [matrixOp, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

@[simp, rep_depth operator]
theorem matrixOp_id [DecidableEq ι] :
    matrixOp (1 : Matrix ι ι ℂ) = ContinuousLinearMap.id ℂ (FinKetSpace ι) := by
  ext x i
  simp [matrixOp, Matrix.one_apply]

/-- Matrix multiplication is operator composition in the AFP pointwise lane. -/
@[rep_depth operator]
theorem matrixOp_comp (B : Matrix τ κ ℂ) (A : Matrix κ ι ℂ) :
    (matrixOp B).comp (matrixOp A) = matrixOp (B * A) := by
  ext x t
  simp [matrixOp, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end MatrixOperators

section Counts

variable {ι : Type u}

/-- Raw finite counts: empirical event counts as pointwise natural-valued functions. -/
@[rep_depth projective]
abbrev CountVector (ι : Type u) := ι → ℕ

/-- Real-valued count/weight vector before projectivization. -/
@[rep_depth projective]
abbrev RealCountVector (ι : Type u) := ι → ℝ

/-- Count atom at index `i`. -/
@[rep_depth projective]
def countAtom [DecidableEq ι] (i : ι) : CountVector ι :=
  Pi.single i (1 : ℕ)

/-- Complex ket lift of a raw count vector. -/
@[rep_depth projective]
def countVectorToKet (c : CountVector ι) : FinKetSpace ι :=
  fun i => (c i : ℂ)

/-- Complex ket lift of a real count/weight vector. -/
@[rep_depth projective]
def realCountVectorToKet (c : RealCountVector ι) : FinKetSpace ι :=
  fun i => (c i : ℂ)

@[simp, rep_depth projective]
theorem countVectorToKet_countAtom [DecidableEq ι] (i : ι) :
    countVectorToKet (countAtom i) = ketPi i := by
  ext j
  by_cases h : j = i
  · subst h
    simp [countVectorToKet, countAtom, ketPi]
  · simp [countVectorToKet, countAtom, ketPi, h]

/-- Projectivized positive count geometry is the existing positive-ray owner. -/
@[rep_depth projective]
abbrev ProjectivePositiveCounts (ι : Type u) [Fintype ι] [Nonempty ι] :=
  PositiveRay ι

end Counts

section MatrixCounts

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ]

/-- Matrix action on raw count vectors after complex ket lift. -/
@[rep_depth operator]
def matrixOpCountKet (A : Matrix κ ι ℂ) (c : CountVector ι) : FinKetSpace κ :=
  matrixOp A (countVectorToKet c)

@[simp, rep_depth operator]
theorem matrixOpCountKet_apply (A : Matrix κ ι ℂ) (c : CountVector ι) (k : κ) :
    matrixOpCountKet A c k = ∑ i : ι, A k i * (c i : ℂ) :=
  rfl

/-- Matrix coefficients are transition weights out of count atoms. -/
@[simp, rep_depth operator]
theorem matrixOpCountKet_countAtom [DecidableEq ι]
    (A : Matrix κ ι ℂ) (i : ι) (k : κ) :
    matrixOpCountKet A (countAtom i) k = A k i := by
  classical
  rw [matrixOpCountKet_apply]
  simp only [countAtom, countVectorToKet, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

end MatrixCounts

end InfoGeometry.Canonical.FiniteKetMatrixCountBridge
