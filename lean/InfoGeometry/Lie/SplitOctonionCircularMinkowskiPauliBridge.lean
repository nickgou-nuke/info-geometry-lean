import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Geometry.PauliParavectorBridge

/-!
# Minkowski diagonal slice and Pauli determinant

The circular `(4,4)` Witt form restricts on the diagonal slice `(u,u)` to
the real `(1,3)` Minkowski form.  This file compares that real slice with the
the canonical Pauli soldering matrix.  Hermiticity is proved for real input;
no positivity or spin-group action is asserted here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge

open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Geometry.PauliParavectorBridge

abbrev Momentum := Fin 4 → ℝ

def minkowskiCoordinates (v : Minkowski4) : Momentum :=
  ![v.t, v.x, v.y, v.z]

def minkowskiSq (u : Momentum) : ℝ :=
  u 0 * u 0 - (u 1 * u 1 + u 2 * u 2 + u 3 * u 3)

def pauliMomentum (u : Momentum) : ℂ × ℂ × ℂ × ℂ :=
  ((u 0 : ℂ), (u 1 : ℂ), (u 2 : ℂ), (u 3 : ℂ))

theorem circularWittQuadratic_diagonal_eq_minkowskiSq (u : Momentum) :
    circularWittQuadratic (minkowskiDiagonalEmbedding u) = minkowskiSq u := by
  simp [minkowskiSq, circularWittQuadratic_minkowskiDiagonal]

theorem pauliMomentum_casimir (u : Momentum) :
    (solder (pauliMomentum u)).det = (minkowskiSq u : ℂ) := by
  rw [casimir_as_determinant]
  simp [pauliMomentum, minkowskiSq]
  ring

theorem circularWittQuadratic_diagonal_eq_pauliDet (u : Momentum) :
    (circularWittQuadratic (minkowskiDiagonalEmbedding u) : ℂ) =
      (solder (pauliMomentum u)).det := by
  rw [pauliMomentum_casimir]
  simp [circularWittQuadratic_diagonal_eq_minkowskiSq]

theorem pauliMatrix_isHermitian (v : Minkowski4) :
    Matrix.conjTranspose (pauliMatrix v) = pauliMatrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix,
      toPauliParavector,
      InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
      Matrix.conjTranspose_apply]
  all_goals ring

theorem circularWittQuadratic_diagonal_eq_minkowski_q
    (v : Minkowski4) :
    circularWittQuadratic (minkowskiDiagonalEmbedding (minkowskiCoordinates v)) = v.q := by
  simp [minkowskiCoordinates, Minkowski4.q, minkowskiSq,
    circularWittQuadratic_diagonal_eq_minkowskiSq]
  ring

theorem circularWittQuadratic_diagonal_eq_canonical_pauliDet
    (v : Minkowski4) :
    (circularWittQuadratic
      (minkowskiDiagonalEmbedding (minkowskiCoordinates v)) : ℂ) =
      Matrix.det (pauliMatrix v) := by
  rw [det_pauliMatrix]
  simp [circularWittQuadratic_diagonal_eq_minkowski_q]

end InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge
