import InfoGeometry.Algebra.RealPauliCausalCone
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitQuaternionAutomorphismStructure

/-!
# Split-quaternion / real indefinite 4-vector owner bridge

This is an algebraic signature bridge, not a Euclidean realization. The
coordinate permutation is `(w,x,y,z) ↦ (t=w,x'=y,y'=x,z'=z)`.
-/

namespace InfoGeometry.Algebra.SplitQuaternionIndefiniteBridge

open InfoGeometry.Algebra.RealPauliCausalCone
open InfoGeometry.Clifford

noncomputable def toRealPauli :
    SplitQuaternion ≃ RealPauliOp where
  toFun := fromSplitQuaternion
  invFun := toSplitQuaternion
  left_inv := by
    intro q
    cases q
    rfl
  right_inv := by
    intro X
    cases X
    rfl

@[simp] theorem toRealPauli_apply (q : SplitQuaternion) :
    toRealPauli q = fromSplitQuaternion q := rfl

@[simp] theorem toSplitQuaternion_toRealPauli (q : SplitQuaternion) :
    toSplitQuaternion (toRealPauli q) = q := by
  cases q
  rfl

@[simp] theorem toRealPauli_toSplitQuaternion (X : RealPauliOp) :
    toRealPauli (toSplitQuaternion X) = X := by
  cases X
  rfl

theorem realPauli_det_signature (q : SplitQuaternion) :
    det (toRealPauli q) = InfoGeometry.Clifford.norm q := by
  exact det_eq_norm (toRealPauli q)

theorem splitQuaternion_norm_signature (w x y z : ℝ) :
    InfoGeometry.Clifford.norm ({ w := w, x := x, y := y, z := z } : SplitQuaternion) =
      w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [InfoGeometry.Clifford.norm]
  ring

end InfoGeometry.Algebra.SplitQuaternionIndefiniteBridge
