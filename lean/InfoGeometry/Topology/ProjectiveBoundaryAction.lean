import Mathlib
import InfoGeometry.Topology.ProjectiveBoundaryUnimodular

namespace InfoGeometry.Topology

/-!
# Actions on the unimodular projective boundary

An action on representatives descends precisely when it preserves the unit
scaling relation.  The preservation obligations are fields rather than
axioms hidden in a quotient lift; a matrix/determinant construction can
instantiate them later.
-/

structure ProjectiveBoundaryAction (R : Type*) [CommRing R] where
  toPair : UnimodularPair R → UnimodularPair R
  respects_units : ∀ {p q : UnimodularPair R},
    unimodularPairRel p q → unimodularPairRel (toPair p) (toPair q)

def ProjectiveBoundaryAction.onBoundary
    {R : Type*} [CommRing R]
    (A : ProjectiveBoundaryAction R) :
    ProjectiveBoundary R → ProjectiveBoundary R :=
  Quotient.lift
    (fun p => projectiveBoundaryMk (A.toPair p))
    (by
      intro p q hpq
      apply Quotient.sound
      exact A.respects_units hpq)

@[simp] theorem ProjectiveBoundaryAction.onBoundary_mk
    {R : Type*} [CommRing R]
    (A : ProjectiveBoundaryAction R) (p : UnimodularPair R) :
    A.onBoundary (projectiveBoundaryMk p) =
      projectiveBoundaryMk (A.toPair p) := rfl

def ProjectiveBoundaryAction.identity
    {R : Type*} [CommRing R] : ProjectiveBoundaryAction R where
  toPair := id
  respects_units := by
    intro p q hpq
    exact hpq

theorem ProjectiveBoundaryAction.identity_onBoundary
    {R : Type*} [CommRing R] (p : ProjectiveBoundary R) :
    ProjectiveBoundaryAction.identity.onBoundary p = p := by
  refine Quotient.inductionOn p ?_
  intro q
  rfl

def ProjectiveBoundaryAction.comp
    {R : Type*} [CommRing R]
    (B A : ProjectiveBoundaryAction R) : ProjectiveBoundaryAction R where
  toPair := B.toPair ∘ A.toPair
  respects_units := by
    intro p q hpq
    exact B.respects_units (A.respects_units hpq)

theorem ProjectiveBoundaryAction.comp_onBoundary
    {R : Type*} [CommRing R]
    (B A : ProjectiveBoundaryAction R) (p : ProjectiveBoundary R) :
    (B.comp A).onBoundary p = B.onBoundary (A.onBoundary p) := by
  refine Quotient.inductionOn p ?_
  intro q
  rfl

end InfoGeometry.Topology
