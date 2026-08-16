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

instance {R : Type*} [CommRing R] : One (ProjectiveBoundaryAction R) :=
  ⟨ProjectiveBoundaryAction.identity⟩

instance {R : Type*} [CommRing R] : Mul (ProjectiveBoundaryAction R) :=
  ⟨fun B A => B.comp A⟩

theorem ProjectiveBoundaryAction.one_mul
    {R : Type*} [CommRing R] (A : ProjectiveBoundaryAction R) :
    (1 : ProjectiveBoundaryAction R) * A = A := by
  cases A
  rfl

theorem ProjectiveBoundaryAction.mul_one
    {R : Type*} [CommRing R] (A : ProjectiveBoundaryAction R) :
    A * (1 : ProjectiveBoundaryAction R) = A := by
  cases A
  rfl

theorem ProjectiveBoundaryAction.mul_assoc
    {R : Type*} [CommRing R]
    (A B C : ProjectiveBoundaryAction R) :
    (A * B) * C = A * (B * C) := by
  cases A
  cases B
  cases C
  rfl

instance {R : Type*} [CommRing R] : Monoid (ProjectiveBoundaryAction R) where
  one := 1
  mul := (· * ·)
  one_mul := ProjectiveBoundaryAction.one_mul
  mul_one := ProjectiveBoundaryAction.mul_one
  mul_assoc := ProjectiveBoundaryAction.mul_assoc

theorem ProjectiveBoundaryAction.comp_onBoundary
    {R : Type*} [CommRing R]
    (B A : ProjectiveBoundaryAction R) (p : ProjectiveBoundary R) :
    (B.comp A).onBoundary p = B.onBoundary (A.onBoundary p) := by
  refine Quotient.inductionOn p ?_
  intro q
  rfl

instance {R : Type*} [CommRing R] :
    SMul (ProjectiveBoundaryAction R) (ProjectiveBoundary R) :=
  ⟨fun A p => A.onBoundary p⟩

instance {R : Type*} [CommRing R] :
    MulAction (ProjectiveBoundaryAction R) (ProjectiveBoundary R) where
  one_smul := ProjectiveBoundaryAction.identity_onBoundary
  mul_smul := by
    intro B A p
    exact ProjectiveBoundaryAction.comp_onBoundary B A p

end InfoGeometry.Topology
