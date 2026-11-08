import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.Quadrics.SignatureDeterminant

Determinant-sign readouts for the canonical homogeneous quadric packets.

This file is deliberately narrow:

* the ellipsoid representative has negative determinant;
* the one-sheet hyperboloid representative has positive determinant;
* the paraboloid representative, written as a block-diagonal homogeneous packet,
  has negative determinant as well.

This is the sign packet only.  It does not prove the full projective
classification of all quadrics.
-/

namespace InfoGeometry.Projective.Quadrics.SignatureDeterminant

open Matrix

/-- Canonical homogeneous representative for the ellipsoid-type quadric. -/
def ellipsoidQuadric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, 1, 1, (-1 : ℝ)]

/-- Canonical homogeneous representative for the one-sheet hyperboloid-type quadric. -/
def hyperboloidQuadric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, 1, (-1 : ℝ), (-1 : ℝ)]

/--
Canonical homogeneous representative for the paraboloid-type projective slice.

The block `!![0, -1; -1, 0]` is a scaled symmetric representative of the
`-zw` cross-term; the scalar factor is irrelevant projectively, while the
determinant sign is stable under nonzero scaling.
-/
def paraboloidQuadric : Matrix (Fin 2 × Bool) (Fin 2 × Bool) ℝ :=
  Matrix.blockDiagonal (fun b : Bool =>
    if b then !![0, (-1 : ℝ); -1, 0]
         else !![1, 0; 0, 1])

/-- The ellipsoid packet has determinant `-1`. -/
theorem det_ellipsoidQuadric : Matrix.det ellipsoidQuadric = (-1 : ℝ) := by
  simp [ellipsoidQuadric, Matrix.det_diagonal, Fin.prod_univ_four]

/-- The one-sheet hyperboloid packet has determinant `+1`. -/
theorem det_hyperboloidQuadric : Matrix.det hyperboloidQuadric = (1 : ℝ) := by
  simp [hyperboloidQuadric, Matrix.det_diagonal, Fin.prod_univ_four]

/-- The paraboloid packet has negative determinant. -/
theorem det_paraboloidQuadric : Matrix.det paraboloidQuadric = (-1 : ℝ) := by
  simp [paraboloidQuadric, Matrix.det_blockDiagonal, Matrix.det_fin_two]

/-- Determinant sign packet for the three canonical homogeneous quadric forms. -/
theorem determinant_sign_packet :
    Matrix.det ellipsoidQuadric = (-1 : ℝ) ∧
    Matrix.det hyperboloidQuadric = (1 : ℝ) ∧
    Matrix.det paraboloidQuadric = (-1 : ℝ) := by
  exact ⟨det_ellipsoidQuadric, det_hyperboloidQuadric, det_paraboloidQuadric⟩

end InfoGeometry.Projective.Quadrics.SignatureDeterminant
