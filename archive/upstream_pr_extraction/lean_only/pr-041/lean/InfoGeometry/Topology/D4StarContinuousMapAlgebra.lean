import InfoGeometry.Topology.D4StarContinuousMapObservables

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Pointwise algebra on descended Mathlib continuous maps. -/

theorem descendedContinuousMap_add
    {Y : Type*} [TopologicalSpace Y] [Add Y] [ContinuousAdd Y]
    (f g : ContinuousOrbitObservable Y) :
    descendedContinuousMap (continuousObservableAdd f g) =
      descendedContinuousMap f + descendedContinuousMap g := by
  ext q
  exact descendContinuousObservable_add f g q

theorem descendedContinuousMap_mul
    {Y : Type*} [TopologicalSpace Y] [Mul Y] [ContinuousMul Y]
    (f g : ContinuousOrbitObservable Y) :
    descendedContinuousMap (continuousObservableMul f g) =
      descendedContinuousMap f * descendedContinuousMap g := by
  ext q
  exact descendContinuousObservable_mul f g q

end InfoGeometry.Topology.PauliJungD4Star
