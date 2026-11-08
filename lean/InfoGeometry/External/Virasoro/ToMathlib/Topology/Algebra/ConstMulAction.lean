import Mathlib.Topology.Algebra.ConstMulAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

def continuousConstSMul_of_discreteTopology (𝕜 X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] [AddCommMonoid X] [SMul 𝕜 X] :
    ContinuousConstSMul 𝕜 X :=
  ⟨fun c ↦ by continuity⟩
