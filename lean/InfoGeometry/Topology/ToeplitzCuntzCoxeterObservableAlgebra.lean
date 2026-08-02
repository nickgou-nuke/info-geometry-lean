import InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The algebraic fixed-point layer of quotient descent

For a topological ring `A`, continuous `A`-valued observables on the ternary
boundary form a ring.  The Coxeter-invariant ones form a `Subring`, and
pullback along the quotient projection is a ring equivalence from continuous
observables on the quotient to that fixed-point subring.

This is an algebraic statement about continuous maps.  It does not assert a
norm completion, a C*-algebra, or any analytic fixed-point theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzCoxeterObservableAlgebra

open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality
open InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

def coxeterOrbitProjectionContinuous :
    C(TernaryBoundary, CoxeterBoundaryOrbitSpace) :=
  { toFun := coxeterOrbitProjection
    continuous_toFun := continuous_coxeterOrbitProjection }

def invariantContinuousSubring :
    Subring C(TernaryBoundary, A) where
  carrier := {f | IsCoxeterInvariant (Y := A) f}
  zero_mem' := by
    intro x
    rfl
  one_mem' := by
    intro x
    rfl
  add_mem' := by
    intro f g hf hg x
    exact congrArg₂ (· + ·) (hf x) (hg x)
  neg_mem' := by
    intro f hf x
    exact congrArg Neg.neg (hf x)
  mul_mem' := by
    intro f g hf hg x
    exact congrArg₂ (· * ·) (hf x) (hg x)

def pullbackContinuousRingHom :
    C(CoxeterBoundaryOrbitSpace, A) →+* invariantContinuousSubring (A := A) :=
  { toFun := fun F =>
      ⟨F.comp coxeterOrbitProjectionContinuous, by
        intro x
        exact congrArg F (coxeterOrbitProjection_identifies_cycle x)⟩
    map_one' := by
      ext x
      rfl
    map_mul' := by
      intro F G
      ext x
      rfl
    map_zero' := by
      ext x
      rfl
    map_add' := by
      intro F G
      ext x
      rfl }

def descentContinuousMap
    (f : invariantContinuousSubring (A := A)) :
    C(CoxeterBoundaryOrbitSpace, A) :=
  { toFun := orbitObservable (Y := A) f f.property
    continuous_toFun :=
      orbitObservable_continuous (Y := A) f f.property f.1.continuous_toFun }

def invariantContinuousRingEquiv :
    C(CoxeterBoundaryOrbitSpace, A) ≃+* invariantContinuousSubring (A := A) where
  toFun := pullbackContinuousRingHom
  invFun := descentContinuousMap
  left_inv := by
    intro F
    ext q
    refine Quotient.inductionOn q ?_
    intro x
    exact orbitObservable_projection
      (Y := A) (F.comp coxeterOrbitProjectionContinuous)
        (pullbackContinuousRingHom (A := A) F).property x
  right_inv := by
    intro f
    ext x
    exact orbitObservable_projection (Y := A) f f.property x
  map_mul' := by
    intro F G
    ext x
    rfl
  map_add' := by
    intro F G
    ext x
    rfl

@[simp] theorem invariantContinuousRingEquiv_apply
    (F : C(CoxeterBoundaryOrbitSpace, A)) :
    invariantContinuousRingEquiv (A := A) F =
      pullbackContinuousRingHom (A := A) F := rfl

end InfoGeometry.Topology.ToeplitzCuntzCoxeterObservableAlgebra
