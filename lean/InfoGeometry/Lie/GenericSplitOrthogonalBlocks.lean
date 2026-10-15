import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Tactic

/-!
# Generic split-orthogonal Lie algebra blocks in a neutral Witt basis

For the finite carrier `Fin n ⊕ Fin n` with Gram matrix
`η = [[0, I], [I, 0]]`, this module characterizes the infinitesimal
isometry equation `Xᵀη + ηX = 0` by its four matrix blocks. This extends the
existing fixed `n = 4` characterization in
`SplitOctonionWittEndomorphismBlockBridge`.

The result is an infinitesimal finite-matrix theorem. It does not assert a
global orthogonal-group factorization, Iwasawa decomposition, or Casimir
classification.
-/

namespace InfoGeometry.Lie.GenericSplitOrthogonalBlocks

open Matrix

variable (n : ℕ)

local instance : LieRing (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :=
  LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ
    (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :=
  LieAlgebra.ofAssociativeAlgebra

abbrev Carrier := Fin n ⊕ Fin n
abbrev SmallMat := Matrix (Fin n) (Fin n) ℝ
abbrev BigMat := Matrix (Carrier n) (Carrier n) ℝ

/-- Neutral Witt pairing on the doubled finite carrier. -/
def etaW : BigMat n := Matrix.fromBlocks 0 1 1 0

/-- Four block coordinates of an endomorphism of the doubled carrier. -/
structure BlockData where
  A : SmallMat n
  B : SmallMat n
  C : SmallMat n
  D : SmallMat n

/-- The endomorphism represented by four Witt-coordinate blocks. -/
def toMatrix (X : BlockData n) : BigMat n :=
  Matrix.fromBlocks X.A X.B X.C X.D

/-- Infinitesimal preservation of the neutral Witt form. -/
def IsWittSkew (X : BlockData n) : Prop :=
  (toMatrix n X)ᵀ * etaW n + etaW n * toMatrix n X = 0

/-- The canonical block equations for the split-orthogonal Lie algebra. -/
def HasWittLieBlocks (X : BlockData n) : Prop :=
  X.D = -X.Aᵀ ∧ X.Bᵀ = -X.B ∧ X.Cᵀ = -X.C

/-- Exact block characterization of the split-orthogonal Lie condition. -/
theorem isWittSkew_iff_hasWittLieBlocks (X : BlockData n) :
    IsWittSkew n X ↔ HasWittLieBlocks n X := by
  dsimp [IsWittSkew, HasWittLieBlocks, toMatrix, etaW]
  rw [Matrix.fromBlocks_transpose]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add]
  rw [Matrix.fromBlocks_add]
  rw [← (Matrix.fromBlocks_zero :
    Matrix.fromBlocks (0 : SmallMat n) 0 0 0 = (0 : BigMat n))]
  rw [Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨?_, ?_, ?_⟩
    · exact eq_neg_of_add_eq_zero_right h₂
    · exact eq_neg_of_add_eq_zero_left h₄
    · exact eq_neg_of_add_eq_zero_left h₁
  · rintro ⟨hD, hB, hC⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hC, neg_add_cancel]
    · rw [hD, add_neg_cancel]
    · rw [hD, Matrix.transpose_neg, Matrix.transpose_transpose, neg_add_cancel]
    · rw [hB, neg_add_cancel]

/-- The native Lie subalgebra of endomorphisms preserving the neutral Witt
form infinitesimally. This uses Mathlib's skew-adjoint matrix subalgebra. -/
noncomputable def splitOrthogonalLieSubalgebra :
    LieSubalgebra ℝ (BigMat n) :=
  skewAdjointMatricesLieSubalgebra (etaW n)

/-- Membership in the split-orthogonal Lie carrier is exactly the neutral
Witt skew-adjoint equation. -/
theorem mem_splitOrthogonalLieSubalgebra_iff (X : BigMat n) :
    X ∈ splitOrthogonalLieSubalgebra n ↔
      Xᵀ * etaW n + etaW n * X = 0 := by
  rw [splitOrthogonalLieSubalgebra,
    mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  change Xᵀ * etaW n = etaW n * (-X) ↔ _
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have h' : Xᵀ * etaW n + etaW n * X = 0 := h
    simpa [mul_neg] using eq_neg_of_add_eq_zero_left h'

/-- The block characterization identifies the native Lie-subalgebra carrier
with the three Witt block equations. -/
theorem toMatrix_mem_splitOrthogonalLieSubalgebra_iff (X : BlockData n) :
    toMatrix n X ∈ splitOrthogonalLieSubalgebra n ↔
      HasWittLieBlocks n X := by
  rw [mem_splitOrthogonalLieSubalgebra_iff]
  exact isWittSkew_iff_hasWittLieBlocks n X

/-! ### The finite split-orthogonal involution

The transpose involution is transported to block coordinates below. Its
restriction preserves the neutral Witt Lie carrier; it is not a group-level
polar decomposition or a proof of positivity for the Killing form. -/

/-- The matrix involution `X ↦ -Xᵀ`, expressed in the four Witt blocks. -/
def cartanThetaBlocks (X : BlockData n) : BlockData n where
  A := -X.Aᵀ
  B := -X.Cᵀ
  C := -X.Bᵀ
  D := -X.Dᵀ

/-- The block formula is exactly negative transpose on the carrier matrix. -/
theorem toMatrix_cartanThetaBlocks (X : BlockData n) :
    toMatrix n (cartanThetaBlocks n X) = -(toMatrix n X)ᵀ := by
  simp [cartanThetaBlocks, toMatrix, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_neg]

/-- The involution preserves the Witt block equations. -/
theorem cartanThetaBlocks_preserves (X : BlockData n)
    (hX : HasWittLieBlocks n X) :
    HasWittLieBlocks n (cartanThetaBlocks n X) := by
  rcases hX with ⟨hD, hB, hC⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp [cartanThetaBlocks]
    rw [hD, Matrix.transpose_neg, Matrix.transpose_transpose]
  · dsimp [cartanThetaBlocks]
    simp [hC]
  · dsimp [cartanThetaBlocks]
    simp [hB]

/-- Applying the transpose involution twice returns the original Witt blocks. -/
theorem cartanThetaBlocks_involutive (X : BlockData n) :
    cartanThetaBlocks n (cartanThetaBlocks n X) = X := by
  cases X
  simp [cartanThetaBlocks, Matrix.transpose_transpose]

/-- Consequently the split-orthogonal block carrier is stable under this
involution. -/
theorem cartanThetaBlocks_maps_lieCarrier (X : BlockData n)
    (hX : toMatrix n X ∈ splitOrthogonalLieSubalgebra n) :
    toMatrix n (cartanThetaBlocks n X) ∈ splitOrthogonalLieSubalgebra n := by
  apply (toMatrix_mem_splitOrthogonalLieSubalgebra_iff n _).mpr
  apply cartanThetaBlocks_preserves
  exact (toMatrix_mem_splitOrthogonalLieSubalgebra_iff n X).mp hX

end InfoGeometry.Lie.GenericSplitOrthogonalBlocks
