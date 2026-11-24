/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FlavorReadout
import InfoGeometry.Streaming.BipartiteGraphDirac
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Pi

/-!
# Real rectangular Dirac and Gram transport

A real rectangular matrix `Y : Matrix m n ℝ` acts between two finite real
coordinate spaces. The existing bipartite owner, instantiated with `Yᵀ`,
gives `D(x,y) = (Y y, Yᵀ x)` and the grading `(x,y) ↦ (x,-y)`.
The native sum/product linear equivalence identifies these operators with
their block matrices. The square has the ordered Gram blocks `Y Yᵀ` and
`Yᵀ Y`; both are positive semidefinite. Their characteristic polynomials
agree after the dimension-dependent powers of `X` are included, so their
nonzero real roots agree.

The signed readout owner feeds this construction directly: arbitrary real
column transformations give a block-diagonal congruence of its Dirac matrix.
This identity does not require orthogonality or assert spectral invariance
for a general congruence.

These are finite operator statements for arbitrary real `Y`. They do not
specify an octonion multiplication, an exceptional symmetry group, a distinct
Krein fundamental symmetry, or an empirical flavor/mass interpretation.
-/

noncomputable section

namespace InfoGeometry.Canonical.FlavorDiracGram

open Matrix
open InfoGeometry.Streaming.BipartiteGraphDirac

variable {m n : Type*}
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The off-diagonal matrix is the existing bipartite Dirac operator under
the native linear equivalence from sum-indexed coordinates to pairs. -/
theorem diracBlock_intertwines (Y : Matrix m n ℝ) (x : m ⊕ n → ℝ) :
    LinearEquiv.sumArrowLequivProdArrow m n ℝ ℝ
        ((fromBlocks (0 : Matrix m m ℝ) Y Yᵀ 0).mulVec x) =
      graphDirac Yᵀ (LinearEquiv.sumArrowLequivProdArrow m n ℝ ℝ x) := by
  rw [graphDirac_apply]
  apply Prod.ext
  · ext i
    simp only [LinearEquiv.sumArrowLequivProdArrow_apply_fst,
      Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero,
      Sum.elim_inl, Matrix.transpose_transpose] <;> rfl
  · ext j
    simp only [LinearEquiv.sumArrowLequivProdArrow_apply_snd,
      Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add, add_zero,
      Sum.elim_inr] <;> rfl

/-- The diagonal sign matrix represents the existing bipartite grading. -/
theorem gradingBlock_intertwines (x : m ⊕ n → ℝ) :
    LinearEquiv.sumArrowLequivProdArrow m n ℝ ℝ
        ((fromBlocks (1 : Matrix m m ℝ) 0 0 (-1 : Matrix n n ℝ)).mulVec x) =
      grading (LinearEquiv.sumArrowLequivProdArrow m n ℝ ℝ x) := by
  apply Prod.ext
  · ext i
    simp [LinearEquiv.sumArrowLequivProdArrow_apply_fst,
      Matrix.fromBlocks_mulVec, grading]
  · ext j
    simp [LinearEquiv.sumArrowLequivProdArrow_apply_snd,
      Matrix.fromBlocks_mulVec, grading]

/-- The represented grading is an involution. -/
theorem gradingBlock_sq :
    fromBlocks (1 : Matrix m m ℝ) 0 0 (-1 : Matrix n n ℝ) *
        fromBlocks (1 : Matrix m m ℝ) 0 0 (-1 : Matrix n n ℝ) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- The existing real Dirac operator has zero anticommutator with grading. -/
theorem dirac_anticommutes_grading (Y : Matrix m n ℝ) :
    grading * graphDirac Yᵀ + graphDirac Yᵀ * grading = 0 := by
  rw [graphDirac_odd]
  exact add_neg_cancel _

/-- Self-adjointness uses the positive real coordinate pairing of the owner. -/
theorem dirac_self_adjoint (Y : Matrix m n ℝ) (x y : Cochain m n) :
    cochainPair (graphDirac Yᵀ x) y =
      cochainPair x (graphDirac Yᵀ y) :=
  graphDirac_adjoint Yᵀ x y

/-- The square of the existing operator acts by the two ordered Gram matrices. -/
theorem dirac_sq_apply (Y : Matrix m n ℝ) (x : Cochain m n) :
    (graphDirac Yᵀ * graphDirac Yᵀ) x =
      ((Y * Yᵀ).mulVec x.1, (Yᵀ * Y).mulVec x.2) := by
  simpa only [Matrix.transpose_transpose, Matrix.mulVec_mulVec] using
    graphDirac_square_blocks Yᵀ x

/-- The same square in sum-indexed matrix coordinates. -/
theorem diracBlock_sq (Y : Matrix m n ℝ) :
    fromBlocks (0 : Matrix m m ℝ) Y Yᵀ 0 *
        fromBlocks (0 : Matrix m m ℝ) Y Yᵀ 0 =
      fromBlocks (Y * Yᵀ) 0 0 (Yᵀ * Y) := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-- Matrix-level oddness for the same grading and Dirac representation. -/
theorem diracBlock_anticommutes_gradingBlock (Y : Matrix m n ℝ) :
    fromBlocks (1 : Matrix m m ℝ) 0 0 (-1 : Matrix n n ℝ) *
        fromBlocks (0 : Matrix m m ℝ) Y Yᵀ 0 +
      fromBlocks (0 : Matrix m m ℝ) Y Yᵀ 0 *
        fromBlocks (1 : Matrix m m ℝ) 0 0 (-1 : Matrix n n ℝ) = 0 := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

/-- Column transformations of the signed operator readout induce the displayed
Dirac-block congruence. The two transformation matrices are arbitrary real
matrices; orthogonality is unnecessary for this identity. -/
theorem readout_diracBlock_basis_change {a b : Type*} [Fintype a] [Fintype b]
    (T : Matrix a b ℝ) (L : Matrix b m ℝ) (R : Matrix a n ℝ)
    (OL : Matrix m m ℝ) (OR : Matrix n n ℝ) :
    fromBlocks (0 : Matrix m m ℝ)
        (FlavorReadout.readout T (L * OL) (R * OR))
        (FlavorReadout.readout T (L * OL) (R * OR))ᵀ 0 =
      fromBlocks OLᵀ 0 0 ORᵀ *
        fromBlocks (0 : Matrix m m ℝ) (FlavorReadout.readout T L R)
          (FlavorReadout.readout T L R)ᵀ 0 *
        fromBlocks OL 0 0 OR := by
  simp only [FlavorReadout.readout_basis_change, Matrix.fromBlocks_multiply,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_zero,
    Matrix.zero_mul, zero_add, add_zero, Matrix.mul_assoc]

/-- The left Gram matrix is positive semidefinite over the real field. -/
theorem leftGram_posSemidef (Y : Matrix m n ℝ) :
    (Y * Yᵀ).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose Y

/-- The right Gram matrix is positive semidefinite over the real field. -/
theorem rightGram_posSemidef (Y : Matrix m n ℝ) :
    (Yᵀ * Y).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self Y

/-- Rectangular Gram characteristic polynomials include the powers of `X`
that account for the different dimensions of the two sectors. -/
theorem gram_charpoly (Y : Matrix m n ℝ) :
    Polynomial.X ^ Fintype.card n * (Y * Yᵀ).charpoly =
      Polynomial.X ^ Fintype.card m * (Yᵀ * Y).charpoly :=
  Matrix.charpoly_mul_comm' Y Yᵀ

/-- For a square real matrix the two Gram characteristic polynomials agree. -/
theorem gram_charpoly_eq (Y : Matrix n n ℝ) :
    (Y * Yᵀ).charpoly = (Yᵀ * Y).charpoly :=
  Matrix.charpoly_mul_comm Y Yᵀ

/-- Away from zero, the dimension factors do not change the real roots.
No equality of rectangular zero-eigenvalue multiplicities is asserted. -/
theorem gram_isRoot_iff_of_ne_zero (Y : Matrix m n ℝ) {μ : ℝ} (hμ : μ ≠ 0) :
    (Y * Yᵀ).charpoly.IsRoot μ ↔ (Yᵀ * Y).charpoly.IsRoot μ := by
  have heval := congrArg (fun p : Polynomial ℝ => p.eval μ) (gram_charpoly Y)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at heval
  change (Y * Yᵀ).charpoly.eval μ = 0 ↔ (Yᵀ * Y).charpoly.eval μ = 0
  constructor
  · intro hleft
    have hright : μ ^ Fintype.card m * (Yᵀ * Y).charpoly.eval μ = 0 := by
      rw [← heval, hleft, mul_zero]
    exact (mul_eq_zero.mp hright).resolve_left (pow_ne_zero _ hμ)
  · intro hright
    have hleft : μ ^ Fintype.card n * (Y * Yᵀ).charpoly.eval μ = 0 := by
      rw [heval, hright, mul_zero]
    exact (mul_eq_zero.mp hleft).resolve_left (pow_ne_zero _ hμ)

end InfoGeometry.Canonical.FlavorDiracGram
