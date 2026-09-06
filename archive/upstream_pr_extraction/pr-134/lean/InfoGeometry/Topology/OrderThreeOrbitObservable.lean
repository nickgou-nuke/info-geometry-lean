import InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient
import InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient

/-!
# Continuous observables on an order-three orbit space

This file formalizes the ordinary quotient-topology descent statement.  An
invariant continuous observable on the carrier descends through the quotient
by an order-three homeomorphism.  No orbifold atlas, manifold structure, or
`G₂` geometry is asserted.
-/

noncomputable section

namespace InfoGeometry.Topology.OrderThreeOrbitObservable

open OrderThreeHomeomorphOrbitQuotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def IsInvariant (h : X ≃ₜ X) (obs : X → Y) : Prop :=
  ∀ x, obs (h x) = obs x

def orbitObservable
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    (obs : X → Y)
    (hinv : IsInvariant h obs) :
    OrbitSpace h hcube → Y :=
  Quotient.lift obs (by
    intro a b hab
    rcases hab with rfl | rfl | rfl
    · rfl
    · exact (hinv a).symm
    · exact ((hinv (h a)).trans (hinv a)).symm)

@[simp] theorem orbitObservable_projection
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    (obs : X → Y)
    (hinv : IsInvariant h obs)
    (x : X) :
    orbitObservable h hcube obs hinv
        (Quotient.mk' (s := orbitSetoid h hcube) x) = obs x := by
  rfl

theorem orbitObservable_mk
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    (obs : X → Y)
    (hinv : IsInvariant h obs)
    (x : X) :
    orbitObservable h hcube obs hinv
        (Quotient.mk' (s := orbitSetoid h hcube) x) = obs x :=
  orbitObservable_projection h hcube obs hinv x

theorem continuous_orbitObservable
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    (obs : X → Y)
    (hinv : IsInvariant h obs)
    (hobs : Continuous obs) :
    Continuous (orbitObservable h hcube obs hinv) := by
  unfold orbitObservable
  exact hobs.quotient_lift _

theorem orbitObservable_unique
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    (obs : X → Y)
    (hinv : IsInvariant h obs)
    (F : OrbitSpace h hcube → Y)
    (hF : ∀ x, F (Quotient.mk' (s := orbitSetoid h hcube) x) = obs x) :
    F = orbitObservable h hcube obs hinv := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact (hF x).trans (orbitObservable_projection h hcube obs hinv x).symm

open InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality

def coxeterObservable
    (obs : TernaryBoundary → Y)
    (hinv : IsInvariant coxeterBoundaryHomeomorph obs) :
    CoxeterBoundaryOrbitSpace → Y :=
  orbitObservable coxeterBoundaryHomeomorph
    coxeterBoundaryHomeomorph_cube obs hinv

theorem continuous_coxeterObservable
    (obs : TernaryBoundary → Y)
    (hinv : IsInvariant coxeterBoundaryHomeomorph obs)
    (hobs : Continuous obs) :
    Continuous (coxeterObservable obs hinv) := by
  exact continuous_orbitObservable coxeterBoundaryHomeomorph
    coxeterBoundaryHomeomorph_cube obs hinv hobs

end InfoGeometry.Topology.OrderThreeOrbitObservable
