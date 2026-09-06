import InfoGeometry.Topology.D4StarContinuousObservables

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Constant zero and one observables for the bundled API. -/

def continuousObservableZero
    {Y : Type*} [TopologicalSpace Y] [Zero Y] :
  ContinuousOrbitObservable Y :=
  ⟨{ toFun := fun _ => 0, continuous_toFun := continuous_const },
    orbitInvariant_zero⟩

def continuousObservableOne
    {Y : Type*} [TopologicalSpace Y] [One Y] :
  ContinuousOrbitObservable Y :=
  ⟨{ toFun := fun _ => 1, continuous_toFun := continuous_const },
    orbitInvariant_one⟩

theorem descendContinuousObservable_zero
    {Y : Type*} [TopologicalSpace Y] [Zero Y]
    (q : D4StarQuotient) :
    descendContinuousObservable (continuousObservableZero (Y := Y)) q = 0 := by
  induction q using Quotient.inductionOn with
  | _ v => rfl

theorem descendContinuousObservable_one
    {Y : Type*} [TopologicalSpace Y] [One Y]
    (q : D4StarQuotient) :
    descendContinuousObservable (continuousObservableOne (Y := Y)) q = 1 := by
  induction q using Quotient.inductionOn with
  | _ v => rfl

end InfoGeometry.Topology.PauliJungD4Star
