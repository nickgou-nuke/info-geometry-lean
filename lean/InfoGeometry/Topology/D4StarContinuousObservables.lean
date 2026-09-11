import InfoGeometry.Topology.D4StarInvariantObservableAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Bundled continuous observables invariant under the orbit relation. -/

abbrev ContinuousOrbitObservable
    (Y : Type*) [TopologicalSpace Y] :=
  {f : C(FourPlaneVertex, Y) // OrbitInvariant f}

namespace ContinuousOrbitObservable

abbrev toFun
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) : FourPlaneVertex → Y := f.1

abbrev invariant
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) : OrbitInvariant f.toFun := f.2

abbrev continuous
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) : Continuous f.toFun := f.1.continuous

end ContinuousOrbitObservable

instance {Y : Type*} [TopologicalSpace Y] :
    CoeFun (ContinuousOrbitObservable Y)
      (fun _ => FourPlaneVertex → Y) :=
  ⟨fun f => f.toFun⟩

def descendContinuousObservable
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) :
    D4StarQuotient → Y :=
  descendObservable f.toFun f.invariant

theorem continuous_descendContinuousObservable
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) :
    Continuous (descendContinuousObservable f) := by
  exact continuous_descendObservable f.toFun f.invariant f.continuous

def continuousObservableAdd
    {Y : Type*} [TopologicalSpace Y] [Add Y] [ContinuousAdd Y]
    (f g : ContinuousOrbitObservable Y) :
  ContinuousOrbitObservable Y :=
  ⟨{ toFun := fun v => f v + g v,
      continuous_toFun := continuous_orbitInvariant_add f.continuous g.continuous },
    orbitInvariant_add f.invariant g.invariant⟩

def continuousObservableMul
    {Y : Type*} [TopologicalSpace Y] [Mul Y] [ContinuousMul Y]
    (f g : ContinuousOrbitObservable Y) :
  ContinuousOrbitObservable Y :=
  ⟨{ toFun := fun v => f v * g v,
      continuous_toFun := continuous_orbitInvariant_mul f.continuous g.continuous },
    orbitInvariant_mul f.invariant g.invariant⟩

theorem descendContinuousObservable_add
    {Y : Type*} [TopologicalSpace Y] [Add Y] [ContinuousAdd Y]
    (f g : ContinuousOrbitObservable Y) (q : D4StarQuotient) :
    descendContinuousObservable (continuousObservableAdd f g) q =
      descendContinuousObservable f q + descendContinuousObservable g q := by
  exact descendObservable_add f.toFun g.toFun f.invariant g.invariant q

theorem descendContinuousObservable_mul
    {Y : Type*} [TopologicalSpace Y] [Mul Y] [ContinuousMul Y]
    (f g : ContinuousOrbitObservable Y) (q : D4StarQuotient) :
    descendContinuousObservable (continuousObservableMul f g) q =
      descendContinuousObservable f q * descendContinuousObservable g q := by
  exact descendObservable_mul f.toFun g.toFun f.invariant g.invariant q

end InfoGeometry.Topology.PauliJungD4Star
