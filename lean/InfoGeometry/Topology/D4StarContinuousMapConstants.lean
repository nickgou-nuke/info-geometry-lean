import InfoGeometry.Topology.D4StarContinuousMapAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Identification of descended constants with Mathlib constant maps. -/

theorem zeroContinuousMapObservable_eq_const
    {Y : Type*} [TopologicalSpace Y] [Zero Y] :
    zeroContinuousMapObservable (Y := Y) =
      ContinuousMap.const D4StarQuotient (0 : Y) := by
  ext q
  exact descendContinuousObservable_zero q

theorem oneContinuousMapObservable_eq_const
    {Y : Type*} [TopologicalSpace Y] [One Y] :
    oneContinuousMapObservable (Y := Y) =
      ContinuousMap.const D4StarQuotient (1 : Y) := by
  ext q
  exact descendContinuousObservable_one q

end InfoGeometry.Topology.PauliJungD4Star
