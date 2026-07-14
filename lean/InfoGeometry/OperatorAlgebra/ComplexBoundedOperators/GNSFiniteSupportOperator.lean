import Mathlib.Analysis.Normed.Module.FiniteDimension
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

/-!
# Finite-support GNS bounded-operator representation

This is the next finite step in the Lean reimplementation of AFP
`Gelfand_Naimark_Segal`.  After constructing the active-support GNS quotient
and proving boundedness of the left action, we package the action as a genuine
mathlib `ContinuousLinearMap`, the Lean analogue of the AFP `action_cblinfun`.
-/

noncomputable section

namespace GNSFiniteSupportOperator

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- Algebraic left action as a linear map on the finite GNS space. -/
def liftLinear (a : Alg n) : GNS p →ₗ[ℂ] GNS p where
  toFun x := liftMul p a x
  map_add' x y := by
    funext i
    simp [liftMul]
    ring
  map_smul' c x := by
    funext i
    simp [liftMul]
    ring

@[simp]
theorem liftLinear_apply (a : Alg n) (x : GNS p) (i : Active p) :
    liftLinear p a x i = a i.1 * x i := by
  rfl

/-- Bounded operator associated to the finite GNS left action. -/
def liftOp (a : Alg n) : GNS p →L[ℂ] GNS p :=
  (liftLinear p a).toContinuousLinearMap

@[simp]
theorem liftOp_apply (a : Alg n) (x : GNS p) (i : Active p) :
    liftOp p a x i = a i.1 * x i := by
  rfl

/-- The bounded representation preserves addition. -/
theorem liftOp_add (a b : Alg n) :
    liftOp p (a + b) = liftOp p a + liftOp p b := by
  apply ContinuousLinearMap.ext
  intro x
  funext i
  simp [liftOp_apply]
  ring

/-- The bounded representation sends algebra multiplication to composition. -/
theorem liftOp_mul (a b : Alg n) :
    liftOp p (fun i => a i * b i) = (liftOp p a).comp (liftOp p b) := by
  apply ContinuousLinearMap.ext
  intro x
  funext i
  simp [liftOp_apply]
  ring

/-- The algebra unit is represented by the identity bounded operator. -/
theorem liftOp_one :
    liftOp p (1 : Alg n) = ContinuousLinearMap.id ℂ (GNS p) := by
  apply ContinuousLinearMap.ext
  intro x
  funext i
  simp [liftOp_apply]

end GNSFiniteSupportOperator
