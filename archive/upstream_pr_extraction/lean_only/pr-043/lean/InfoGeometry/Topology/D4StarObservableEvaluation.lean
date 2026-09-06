import InfoGeometry.Topology.D4StarContinuousMapConstants

namespace InfoGeometry.Topology.PauliJungD4Star

/-! Evaluation morphisms for quotient-valued observables. -/

def observableEvaluationAddMonoidHom
    {Y : Type*} [TopologicalSpace Y] [AddMonoid Y] [ContinuousAdd Y]
    (q : D4StarQuotient) :
    C(D4StarQuotient, Y) →+ Y :=
  { toFun := fun f => f q
    map_zero' := by rfl
    map_add' := by intro f g; rfl }

def observableEvaluationMonoidHom
    {Y : Type*} [TopologicalSpace Y] [Monoid Y] [ContinuousMul Y]
    (q : D4StarQuotient) :
    C(D4StarQuotient, Y) →* Y :=
  { toFun := fun f => f q
    map_one' := by rfl
    map_mul' := by intro f g; rfl }

theorem observableEvaluationAddMonoidHom_apply
    {Y : Type*} [TopologicalSpace Y] [AddMonoid Y] [ContinuousAdd Y]
    (q : D4StarQuotient)
    (f : C(D4StarQuotient, Y)) :
    observableEvaluationAddMonoidHom q f = f q := rfl

theorem observableEvaluationMonoidHom_apply
    {Y : Type*} [TopologicalSpace Y] [Monoid Y] [ContinuousMul Y]
    (q : D4StarQuotient)
    (f : C(D4StarQuotient, Y)) :
    observableEvaluationMonoidHom q f = f q := rfl

theorem observableEvaluation_descended
    {Y : Type*} [TopologicalSpace Y]
    (f : ContinuousOrbitObservable Y) (q : D4StarQuotient) :
    descendedContinuousMap f q = descendContinuousObservable f q := rfl

end InfoGeometry.Topology.PauliJungD4Star
