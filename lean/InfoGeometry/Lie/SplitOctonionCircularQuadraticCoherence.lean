import InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge
import InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates

/-!
# Coherence of the transported and explicit circular quadratic forms

`circularPeirceQuadratic` is the native determinant transported through the
genuine circular basis.  `circularWittQuadratic` is its explicit Witt
polynomial.  This owner records their equality and transports the existing
Minkowski/Pauli diagonal theorem back to the native quadratic form.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence

open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge
open InfoGeometry.Geometry.PauliParavectorBridge

theorem circularPeirceQuadratic_eq_circularWittQuadratic (x : Fin 8 → ℝ) :
    circularPeirceQuadratic x = circularWittQuadratic x := by
  rw [circularPeirceQuadratic_formula]
  rfl

theorem circularPeirceQuadratic_diagonal_eq_minkowski_q
    (v : Minkowski4) :
    circularPeirceQuadratic
        (minkowskiDiagonalEmbedding (minkowskiCoordinates v)) = v.q := by
  rw [circularPeirceQuadratic_eq_circularWittQuadratic]
  exact circularWittQuadratic_diagonal_eq_minkowski_q v

theorem circularPeirceQuadratic_diagonal_eq_canonical_pauliDet
    (v : Minkowski4) :
    (circularPeirceQuadratic
        (minkowskiDiagonalEmbedding (minkowskiCoordinates v)) : ℂ) =
      Matrix.det (pauliMatrix v) := by
  rw [circularPeirceQuadratic_diagonal_eq_minkowski_q]
  exact (det_pauliMatrix v).symm ▸ rfl

end InfoGeometry.Lie.SplitOctonionCircularQuadraticCoherence
