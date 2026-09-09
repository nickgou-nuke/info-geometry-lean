import InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-!
# Rational circular dual coordinates

The finite matrix export uses coordinates of the rational frame.  This file
defines the separate rational dual functionals corresponding to the real
`circularCoordinate` owner and proves their scalar-extension compatibility.
-/

namespace InfoGeometry.Lie.CanonicalZornG2RationalCircularCoordinates

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

abbrev RationalVZ := ZornVectorMatrix ℚ

def rationalCircularCoordinate (X : RationalVZ) : Fin 8 → ℚ
  | 0 => X.a + X.b
  | 1 => X.v 0 + X.w 0
  | 2 => X.v 1 + X.w 1
  | 3 => X.v 2 + X.w 2
  | 4 => X.a - X.b
  | 5 => X.w 0 - X.v 0
  | 6 => X.w 1 - X.v 1
  | 7 => X.w 2 - X.v 2
  | _ => 0

def rationalToCartesian (X : RationalVZ) : CartesianCoordinates :=
  Prod.mk (Prod.mk (X.a : ℝ) (fun i => (X.v i : ℝ)))
    (Prod.mk (X.b : ℝ) (fun i => (X.w i : ℝ)))

theorem rationalCircularCoordinate_cast (X : RationalVZ) (i : Fin 8) :
    (rationalCircularCoordinate X i : ℝ) =
      circularCoordinate (rationalToCartesian X) i := by
  fin_cases i <;>
    simp [rationalCircularCoordinate, rationalToCartesian,
      circularCoordinate]

theorem rationalCircularFrame_reconstruct_cast (X : RationalVZ) :
    (∑ i : Fin 8,
      (rationalCircularCoordinate X i : ℝ) •
        cartesianZornLinearEquiv (circularFrame i)) =
      cartesianZornLinearEquiv (rationalToCartesian X) := by
  calc
    (∑ i : Fin 8,
        (rationalCircularCoordinate X i : ℝ) •
          cartesianZornLinearEquiv (circularFrame i)) =
        ∑ i : Fin 8,
          circularCoordinate (rationalToCartesian X) i •
            cartesianZornLinearEquiv (circularFrame i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [rationalCircularCoordinate_cast]
    _ = cartesianZornLinearEquiv
          (∑ i : Fin 8,
            circularCoordinate (rationalToCartesian X) i • circularFrame i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
    _ = cartesianZornLinearEquiv (rationalToCartesian X) := by
      rw [circularFrame_reconstruct]

theorem rationalCircularFrame_reconstruct_diag (X : RationalVZ) :
    (∑ i : Fin 8,
      (rationalCircularCoordinate X i : ℝ) •
        (InfoGeometry.Lie.SplitOctonionEllClosedFlow.diagCircularBasis i)) =
      cartesianZornLinearEquiv (rationalToCartesian X) := by
  simp only [InfoGeometry.Lie.SplitOctonionEllClosedFlow.diagCircularBasis_apply]
  simpa [InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularBasis_apply] using
    rationalCircularFrame_reconstruct_cast X

/-! The rational frame has the same transported vectors as the real owner
    basis.  This is the basis-level scalar-extension bridge; it is kept
    separate from coordinate reconstruction so matrix transport can use it
    without expanding a matrix inverse. -/
theorem rationalCircularFrame_cast_eq_diagCircularBasis (i : Fin 8) :
    cartesianZornLinearEquiv (rationalToCartesian (rationalCircularFrame i)) =
      InfoGeometry.Lie.SplitOctonionEllClosedFlow.diagCircularBasis i := by
  rw [InfoGeometry.Lie.SplitOctonionEllClosedFlow.diagCircularBasis_apply]
  fin_cases i <;>
    simp only [rationalCircularFrame, rationalToCartesian,
      rationalFrameVector, circularFrame,
      scalarPlus, scalarMinus, rootPlus, rootMinus,
      InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis.circularBasis_apply]
    <;> ext <;> simp [quaternionScalar, ellScalar, quaternionAxis,
      ellAxis, axis, Pi.single_apply, smul_eq_mul, zeroVec3, rationalAxis] <;>
    (try split_ifs) <;> (try { subst_vars; contradiction }) <;> norm_num

end InfoGeometry.Lie.CanonicalZornG2RationalCircularCoordinates
