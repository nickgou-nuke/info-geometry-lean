import InfoGeometry.Topology.D4StarFiniteStateFunctionalConvexity

namespace InfoGeometry.Topology.PauliJungD4Star

/-! The finite observable algebra has a commutative trace condition. -/

def FiniteTraceCondition (ω : FiniteStateFunctional) : Prop :=
  ∀ f g : C(D4StarQuotient, ℚ), ω (f * g) = ω (g * f)

theorem affineStateFunctional_traceCondition
    (s : BooleanAffineState) :
    FiniteTraceCondition (affineStateFunctional s) := by
  intro f g
  simp [FiniteTraceCondition, affineStateFunctional, affineExpectation]
  ring

theorem uniformFiniteTraceCondition :
    FiniteTraceCondition (affineStateFunctional uniformBooleanAffineState) :=
  affineStateFunctional_traceCondition uniformBooleanAffineState

end InfoGeometry.Topology.PauliJungD4Star
