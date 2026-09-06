import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportOperator

/-!
# Inner-product laws for the finite-support GNS bounded representation

This continues the step-by-step Lean reimplementation of AFP
`Gelfand_Naimark_Segal`.  Since the finite active-support GNS space in this
layer is represented by a plain function type with an explicit inner product
`innerGNS`, the adjoint/*-representation law is proved directly relative to
that inner product.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportOperatorInner

open GNSFiniteSupport
open GNSFiniteSupportOperator

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- Acting on the cyclic vector gives the restricted algebra element. -/
theorem liftOp_omegaVec_eq_restrict (a : Alg n) :
    liftOp p a (omegaVec p) = restrict p a := by
  funext i
  simp [liftOp_apply, omegaVec, restrict]

/-- Vector-state recovery using the bounded-operator representation. -/
theorem liftOp_vector_state_recovers_omega (a : Alg n) :
    innerGNS p (omegaVec p) (liftOp p a (omegaVec p)) = omega p a := by
  rw [liftOp_omegaVec_eq_restrict]
  exact vector_state_recovers_omega p a

/-- Cyclicity for the bounded-operator orbit of `omegaVec`. -/
theorem liftOp_cyclic_property (x : GNS p) :
    ∃ a : Alg n, liftOp p a (omegaVec p) = x := by
  rcases cyclic_property p x with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [liftOp_omegaVec_eq_restrict]
  exact ha

/-- Explicit GNS inner-product adjoint law for finite-support multiplication. -/
theorem liftOp_inner_adjoint_relation (a : Alg n) (x y : GNS p) :
    innerGNS p (liftOp p a x) y = innerGNS p x (liftOp p (involution a) y) := by
  unfold innerGNS
  apply Finset.sum_congr rfl
  intro i _
  simp [liftOp_apply, involution]
  ring

/-- Positive squares are represented as composition with the involuted action. -/
theorem liftOp_positive_square_comp (a : Alg n) :
    liftOp p (fun i => involution a i * a i) = (liftOp p (involution a)).comp (liftOp p a) := by
  apply ContinuousLinearMap.ext
  intro x
  funext i
  simp [liftOp_apply]
  ring

/-- Cyclic coefficient of a positive square equals the state value. -/
theorem liftOp_positive_square_state (a : Alg n) :
    innerGNS p (omegaVec p) (liftOp p (fun i => involution a i * a i) (omegaVec p)) =
      omega p (fun i => involution a i * a i) := by
  exact liftOp_vector_state_recovers_omega p (fun i => involution a i * a i)

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupportOperatorInner
