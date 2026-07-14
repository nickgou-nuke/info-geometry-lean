import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

/-!
# Boundedness of the finite-support GNS left action

This continues the finite Lean reimplementation of AFP
`Gelfand_Naimark_Segal`.  In the AFP construction, the algebraic left action is
shown bounded before it is extended to a bounded operator on the completed GNS
space.  Here the corresponding finite-support inequality is proved directly.
-/

noncomputable section

namespace GNSFiniteSupportBounded

open scoped BigOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- Pointwise squared norm of the left action factors. -/
theorem liftMul_norm_sq_apply (a : Alg n) (x : GNS p) (i : Active p) :
    ‖liftMul p a x i‖ ^ 2 = ‖a i.1‖ ^ 2 * ‖x i‖ ^ 2 := by
  simp [liftMul, pow_two]
  ring

/-- A coordinate bound gives a pointwise bound on each summand. -/
theorem liftMul_norm_sq_apply_le
    (a : Alg n) (x : GNS p) (K : ℝ)
    (hK : ∀ i : Active p, ‖a i.1‖ ^ 2 ≤ K)
    (i : Active p) :
    ‖liftMul p a x i‖ ^ 2 ≤ K * ‖x i‖ ^ 2 := by
  rw [liftMul_norm_sq_apply]
  exact mul_le_mul_of_nonneg_right (hK i) (sq_nonneg ‖x i‖)

/-- Finite boundedness estimate for the GNS left action. -/
theorem liftMul_norm_bound
    (a : Alg n) (x : GNS p) (K : ℝ)
    (hK : ∀ i : Active p, ‖a i.1‖ ^ 2 ≤ K) :
    normInnerGNS p (liftMul p a x) ≤ K * normInnerGNS p x := by
  unfold normInnerGNS
  calc
    (∑ i : Active p, ‖liftMul p a x i‖ ^ 2)
        ≤ ∑ i : Active p, K * ‖x i‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _ => liftMul_norm_sq_apply_le p a x K hK i
    _ = K * ∑ i : Active p, ‖x i‖ ^ 2 := by
          rw [Finset.mul_sum]

/-- Null vectors remain null after left multiplication. -/
theorem liftMul_preserves_null
    (a : Alg n) (x : Alg n)
    (hx : nullSubspace p x) :
    nullSubspace p (fun i => a i * x i) := by
  intro i
  simp [hx i]

/-- The left action is well-defined on GNS equivalence classes. -/
theorem liftMul_respects_same_gns
    (a x y : Alg n)
    (hxy : restrict p x = restrict p y) :
    restrict p (fun i => a i * x i) = restrict p (fun i => a i * y i) := by
  funext i
  have hi := congrFun hxy i
  simp [restrict] at hi
  simp [restrict, hi]

end GNSFiniteSupportBounded
