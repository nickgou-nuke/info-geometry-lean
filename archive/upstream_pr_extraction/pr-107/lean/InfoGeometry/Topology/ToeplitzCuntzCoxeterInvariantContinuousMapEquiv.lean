import InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapAlgebra

/-!
# Continuous-map equivalence for the Coxeter orbit quotient

This packages the quotient universal property as an equivalence of continuous
maps.  The codomain is arbitrary and may later carry additional algebraic
structure.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapEquiv

open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
open InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality

variable {Y : Type*} [TopologicalSpace Y]

abbrev InvariantContinuousMap :=
  {f : C(TernaryBoundary, Y) // IsCoxeterInvariant f}

def pullbackOrbitObservable
    (F : C(CoxeterBoundaryOrbitSpace, Y)) : InvariantContinuousMap (Y := Y) :=
  ⟨{ toFun := fun x => F (coxeterOrbitProjection x),
      continuous_toFun := F.continuous.comp continuous_coxeterOrbitProjection }, by
    intro x
    change F (coxeterOrbitProjection (coxeterBoundaryHomeomorph x)) =
      F (coxeterOrbitProjection x)
    rw [coxeterOrbitProjection_identifies_cycle]⟩

def descendOrbitObservable
    (f : InvariantContinuousMap (Y := Y)) :
    C(CoxeterBoundaryOrbitSpace, Y) :=
  { toFun := orbitObservable f.val f.property
    continuous_toFun := orbitObservable_continuous f.val f.property f.val.continuous }

@[simp] theorem descendOrbitObservable_apply_projection
    (f : InvariantContinuousMap (Y := Y))
    (x : TernaryBoundary) :
    descendOrbitObservable f (coxeterOrbitProjection x) = f.val x := by
  exact orbitObservable_projection f.val f.property x

@[simp] theorem descend_pullback
    (F : C(CoxeterBoundaryOrbitSpace, Y)) :
    descendOrbitObservable (pullbackOrbitObservable F) = F := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  unfold descendOrbitObservable pullbackOrbitObservable
  change F (coxeterOrbitProjection x) = F (coxeterOrbitProjection x)
  rfl

@[simp] theorem pullback_descend
    (f : InvariantContinuousMap (Y := Y)) :
    pullbackOrbitObservable (descendOrbitObservable f) = f := by
  apply Subtype.ext
  ext x
  change descendOrbitObservable f (coxeterOrbitProjection x) = f.val x
  exact descendOrbitObservable_apply_projection f x

def orbitContinuousMapEquiv :
    C(CoxeterBoundaryOrbitSpace, Y) ≃ InvariantContinuousMap (Y := Y) where
  toFun := pullbackOrbitObservable
  invFun := descendOrbitObservable
  left_inv := descend_pullback
  right_inv := pullback_descend

@[simp] theorem orbitContinuousMapEquiv_apply
    (F : C(CoxeterBoundaryOrbitSpace, Y)) :
    orbitContinuousMapEquiv (Y := Y) F = pullbackOrbitObservable F := rfl

@[simp] theorem orbitContinuousMapEquiv_symm_apply
    (f : InvariantContinuousMap (Y := Y)) :
    (orbitContinuousMapEquiv (Y := Y)).symm f = descendOrbitObservable f := rfl

end InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousMapEquiv
