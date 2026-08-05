import Mathlib.Topology.ContinuousMap.Star
import InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables

/-!
# Coxeter-invariant continuous map algebra on the ternary boundary quotient

This file packages the same order-three quotient descent as a `ContinuousMap`
into the quotient space and records the pointwise algebraic laws on the
descended observables. It does not claim any additional physics or geometry.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapAlgebra

open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
open InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality

/-- Bundled continuous observables on the concrete ternary boundary. -/
abbrev ContinuousCoxeterObservable (A : Type*) [TopologicalSpace A] :=
  {f : C(TernaryBoundary, A) // IsCoxeterInvariant f}

namespace ContinuousCoxeterObservable

abbrev toFun
    {A : Type*} [TopologicalSpace A]
    (f : ContinuousCoxeterObservable A) : TernaryBoundary → A := f.1

abbrev invariant
    {A : Type*} [TopologicalSpace A]
    (f : ContinuousCoxeterObservable A) : IsCoxeterInvariant f.toFun := f.2

abbrev continuous
    {A : Type*} [TopologicalSpace A]
    (f : ContinuousCoxeterObservable A) : Continuous f.toFun := f.1.continuous

end ContinuousCoxeterObservable

instance {A : Type*} [TopologicalSpace A] : CoeFun (ContinuousCoxeterObservable A)
    (fun _ => TernaryBoundary → A) :=
  ⟨fun f => f.toFun⟩

/-- Descend a bundled continuous observable through the coarse orbit quotient. -/
def descendedContinuousMap {A : Type*} [TopologicalSpace A]
    (f : ContinuousCoxeterObservable A) :
    C(CoxeterBoundaryOrbitSpace, A) :=
  { toFun := orbifoldObservable f.toFun f.invariant
    continuous_toFun := orbifoldObservable_continuous f.toFun f.invariant f.continuous }

@[simp] theorem descendedContinuousMap_apply
    {A : Type*} [TopologicalSpace A]
    (f : ContinuousCoxeterObservable A)
    (q : CoxeterBoundaryOrbitSpace) :
    descendedContinuousMap f q = orbifoldObservable f.toFun f.invariant q := rfl

@[simp] theorem descendedContinuousMap_comp_projection
    {A : Type*} [TopologicalSpace A]
    (f : ContinuousCoxeterObservable A)
    (x : TernaryBoundary) :
    descendedContinuousMap f (coxeterOrbitProjection x) = f x := by
  exact orbifoldObservable_projection f.toFun f.invariant x

section PointwiseAlgebra

variable {A : Type*} [TopologicalSpace A]
variable [Add A] [ContinuousAdd A]
variable [Mul A] [ContinuousMul A]
variable [Star A] [ContinuousStar A]

def continuousObservableAdd
    (f g : ContinuousCoxeterObservable A) :
  ContinuousCoxeterObservable A :=
  ⟨{ toFun := fun x => f x + g x,
      continuous_toFun := f.continuous.add g.continuous }, by
      intro x
      simp [f.invariant x, g.invariant x]⟩

def continuousObservableMul
    (f g : ContinuousCoxeterObservable A) :
  ContinuousCoxeterObservable A :=
  ⟨{ toFun := fun x => f x * g x,
      continuous_toFun := f.continuous.mul g.continuous }, by
      intro x
      simp [f.invariant x, g.invariant x]⟩

def continuousObservableStar
    (f : ContinuousCoxeterObservable A) :
  ContinuousCoxeterObservable A :=
  ⟨{ toFun := fun x => star (f x),
      continuous_toFun := continuous_star.comp f.continuous }, by
      intro x
      simpa using congrArg star (f.invariant x)⟩

theorem descendedContinuousMap_add
    (f g : ContinuousCoxeterObservable A) :
    descendedContinuousMap (continuousObservableAdd f g) =
      descendedContinuousMap f + descendedContinuousMap g := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  change (f.toFun x + g.toFun x) = f.toFun x + g.toFun x
  rfl

theorem descendedContinuousMap_mul
    (f g : ContinuousCoxeterObservable A) :
    descendedContinuousMap (continuousObservableMul f g) =
      descendedContinuousMap f * descendedContinuousMap g := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  change (f.toFun x * g.toFun x) = f.toFun x * g.toFun x
  rfl

theorem descendedContinuousMap_star
    (f : ContinuousCoxeterObservable A) :
    descendedContinuousMap (continuousObservableStar f) =
      star (descendedContinuousMap f) := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  change star (f.toFun x) = star (f.toFun x)
  rfl

end PointwiseAlgebra

end InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapAlgebra
