import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Lie.SplitOctonionCrossTensor

/-!
# Orientation reversal of the second quaternionic three-channel

The optional display order `(ell i, ell k, ell j)` is one transposition of
the paired order `(ell i, ell j, ell k)`.  This owner models that operation
*after* the `e_a <-> ell e_a` circular pairing.  It therefore does not alter
the root eigenvectors; it only records the induced sign on the oriented
three-dimensional cross/volume tensor.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCrossTensor
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

abbrev V3 := Fin 3 → ℝ

/-- The coordinate transposition `(i,j,k) -> (i,k,j)`. -/
def swapJK : V3 ≃ₗ[ℝ] V3 where
  toFun v := ![v 0, v 2, v 1]
  invFun v := ![v 0, v 2, v 1]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' u v := by funext i; fin_cases i <;> rfl
  map_smul' c v := by funext i; fin_cases i <;> rfl

@[simp] theorem swapJK_apply_zero (v : V3) : swapJK v 0 = v 0 := rfl
@[simp] theorem swapJK_apply_one (v : V3) : swapJK v 1 = v 2 := rfl
@[simp] theorem swapJK_apply_two (v : V3) : swapJK v 2 = v 1 := rfl

theorem swapJK_involutive (v : V3) : swapJK (swapJK v) = v :=
  swapJK.symm_apply_apply v

/-- The transposition is orthogonal for the native three-coordinate dot
pairing. -/
theorem dot_swapJK (u v : V3) :
    dot (swapJK u) (swapJK v) = dot u v := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- One transposition reverses the oriented scalar triple product. -/
theorem nativeScalarTriple_swapJK (u v w : V3) :
    nativeScalarTriple (swapJK u) (swapJK v) (swapJK w) =
      -nativeScalarTriple u v w := by
  rw [nativeScalarTriple_eq_det3, nativeScalarTriple_eq_det3]
  simp [swapJK, InfoGeometry.Physics.ZornMatrixSU3.det3]
  ring

/-- Equivalently, the cross product acquires the determinant sign of the
orientation-reversing transposition. -/
theorem cross_swapJK (u v : V3) :
    cross (swapJK u) (swapJK v) = -swapJK (cross u v) := by
  funext i
  fin_cases i <;>
    simp [swapJK, InfoGeometry.Canonical.ZornMatrix.cross,
      InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]

/-- The optional ordering is a post-pairing permutation: it fixes the first
axis and interchanges only the second and third `ell` partners. -/
theorem swapJK_axes :
    swapJK (axis 0) = axis 0 ∧
      swapJK (axis 1) = axis 2 ∧
      swapJK (axis 2) = axis 1 := by
  constructor
  · funext i
    fin_cases i <;> simp [axis]
  constructor <;> funext i <;> fin_cases i <;> simp [axis]

end InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation
