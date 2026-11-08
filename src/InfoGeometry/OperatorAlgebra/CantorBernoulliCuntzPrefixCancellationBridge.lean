import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Prefix cancellation for the concrete Cantor Cuntz word operators

The matrix-unit owner deliberately handles only equal-depth words.  This
owner supplies the two nonzero prefix cases needed before an unrestricted
algebraic word-product/KMS theorem can be stated.  It remains a finite
operator theorem on the concrete bounded-operator carrier; no quotient or
completion is introduced here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzPrefixCancellationBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

theorem operatorWordDag_comp_operatorWord_prefix
    (v w : List Bool) :
    (operatorWordDag v).comp (operatorWord (v ++ w)) = operatorWord w := by
  rw [operatorWord_append]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [operatorWordDag_comp_operatorWord]
  simp

theorem operatorWordDag_comp_operatorWord_suffix
    (x w : List Bool) :
    (operatorWordDag (x ++ w)).comp (operatorWord x) = operatorWordDag w := by
  rw [operatorWordDag_append]
  rw [ContinuousLinearMap.comp_assoc]
  rw [operatorWordDag_comp_operatorWord]
  simp

theorem operatorMatrixUnit_mul_right_prefix
    (u v w y : List Bool) :
    (operatorMatrixUnit u v).comp
        (operatorMatrixUnit (v ++ w) y) =
      operatorMatrixUnit (u ++ w) y := by
  apply ContinuousLinearMap.ext
  intro f
  unfold operatorMatrixUnit
  change operatorWord u
      (operatorWordDag v
        (operatorWord (v ++ w)
          (operatorWordDag y f))) = _
  have h := ContinuousLinearMap.ext_iff.mp
    (operatorWordDag_comp_operatorWord_prefix v w) (operatorWordDag y f)
  have h' : operatorWordDag v
      (operatorWord (v ++ w) (operatorWordDag y f)) =
      operatorWord w (operatorWordDag y f) := by
    simpa using h
  rw [h']
  simp [operatorWord_append, ContinuousLinearMap.comp_assoc]

theorem operatorMatrixUnit_mul_left_prefix
    (u x w y : List Bool) :
    (operatorMatrixUnit u (x ++ w)).comp
        (operatorMatrixUnit x y) =
      operatorMatrixUnit u (y ++ w) := by
  apply ContinuousLinearMap.ext
  intro f
  unfold operatorMatrixUnit
  change operatorWord u
      (operatorWordDag (x ++ w)
        (operatorWord x (operatorWordDag y f))) = _
  have h := ContinuousLinearMap.ext_iff.mp
    (operatorWordDag_comp_operatorWord_suffix x w) (operatorWordDag y f)
  have h' : operatorWordDag (x ++ w)
      (operatorWord x (operatorWordDag y f)) =
      operatorWordDag w (operatorWordDag y f) := by
    simpa using h
  rw [h']
  have hdag := ContinuousLinearMap.ext_iff.mp
    (operatorWordDag_append y w) f
  simpa using hdag.symm ▸ rfl

end InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzPrefixCancellationBridge
