import InfoGeometry.Topology.D4StarInvariantObservables
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Orbit-invariant observables are constant along the induced hidden flow. -/

theorem descendObservable_inducedFlow_invariant
    {Y : Type*} (f : FourPlaneVertex → Y)
    (hf : OrbitInvariant f) (t : ℤ) (q : D4StarQuotient) :
    descendObservable f hf ((inducedQuotientFlow
      trivialColorPermutationFlow).flow t q) =
      descendObservable f hf q := by
  rw [inducedQuotientFlow_is_trivial]

theorem continuous_descendObservable_inducedFlow_invariant
    {Y : Type*} [TopologicalSpace Y]
    (f : FourPlaneVertex → Y) (hf : OrbitInvariant f)
    (hcont : Continuous f) (t : ℤ) (q : D4StarQuotient) :
    descendObservable f hf ((inducedQuotientFlow
      trivialColorPermutationFlow).flow t q) =
      descendObservable f hf q :=
  descendObservable_inducedFlow_invariant f hf t q

end InfoGeometry.Topology.PauliJungD4Star
