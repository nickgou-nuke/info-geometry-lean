import InfoGeometry.Topology.KleinRealOperatorDescent

noncomputable section

namespace InfoGeometry.Topology.KleinPointwiseOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient
open InfoGeometry.Topology.KleinRealOperatorDescent

variable {Carrier : Type*} [AddCommGroup Carrier] [Module ℝ Carrier]

theorem pointwise_preserves_invariants (operator : Module.End ℝ Carrier)
    (field : invariantFields (V := Carrier)) :
    operator.compLeft BrillouinTorus field ∈ invariantFields := by
  intro point
  exact congrArg operator (field.property point)

def descendedPointwise (operator : Module.End ℝ Carrier) :
    Module.End ℝ (KleinBrillouinQuotient → Carrier) :=
  quotientOperator (operator.compLeft BrillouinTorus) (pointwise_preserves_invariants operator)

theorem descendedPointwise_eq (operator : Module.End ℝ Carrier) :
    descendedPointwise operator = operator.compLeft KleinBrillouinQuotient := by
  symm
  apply quotientOperator_unique
  intro field point
  rfl

@[simp] theorem descendedPointwise_apply (operator : Module.End ℝ Carrier)
    (field : KleinBrillouinQuotient → Carrier) (point : KleinBrillouinQuotient) :
    descendedPointwise operator field point = operator (field point) := by
  rw [descendedPointwise_eq]
  rfl

theorem descendedPointwise_mul (first second : Module.End ℝ Carrier) :
    descendedPointwise (first * second) = descendedPointwise first * descendedPointwise second := by
  ext field point
  simp only [Module.End.mul_apply, descendedPointwise_apply]

theorem descendedPointwise_kernel_iff (operator : Module.End ℝ Carrier)
    (field : KleinBrillouinQuotient → Carrier) :
    field ∈ LinearMap.ker (descendedPointwise operator) ↔
      ∀ point, field point ∈ LinearMap.ker operator := by
  change descendedPointwise operator field = 0 ↔ ∀ point, operator (field point) = 0
  constructor
  · intro killed point
    simpa only [descendedPointwise_apply, Pi.zero_apply] using congrFun killed point
  · intro killed
    funext point
    exact (descendedPointwise_apply operator field point).trans (killed point)

end InfoGeometry.Topology.KleinPointwiseOperatorDescent
