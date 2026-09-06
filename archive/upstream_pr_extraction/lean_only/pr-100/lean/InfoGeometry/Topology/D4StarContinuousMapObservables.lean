import InfoGeometry.Topology.D4StarContinuousObservableConstants

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Descended observables as native Mathlib continuous maps. -/

def descendedContinuousMap
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) :
    C(D4StarQuotient, Y) :=
  { toFun := descendContinuousObservable f
    continuous_toFun := continuous_descendContinuousObservable f }

@[simp] theorem descendedContinuousMap_apply
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) (q : D4StarQuotient) :
    descendedContinuousMap f q = descendContinuousObservable f q := rfl

theorem descendedContinuousMap_comp_projection
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) (v : FourPlaneVertex) :
    descendedContinuousMap f (starQuotientMap v) = f v := by
  exact descendObservable_comp f.toFun f.invariant v

def zeroContinuousMapObservable
    {Y : Type*} [TopologicalSpace Y] [Zero Y] :
    C(D4StarQuotient, Y) :=
  descendedContinuousMap (continuousObservableZero (Y := Y))

def oneContinuousMapObservable
    {Y : Type*} [TopologicalSpace Y] [One Y] :
    C(D4StarQuotient, Y) :=
  descendedContinuousMap (continuousObservableOne (Y := Y))

end InfoGeometry.Topology.PauliJungD4Star
