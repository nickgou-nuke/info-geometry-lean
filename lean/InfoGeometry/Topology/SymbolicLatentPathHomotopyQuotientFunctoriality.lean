import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentPathHomotopyFunctoriality

namespace InfoGeometry.Topology

/-!
# Functoriality of symbolic-latent path homotopy quotients

Continuous maps descend through the homotopy quotient because they preserve
the endpoint-preserving homotopy relation.  The endpoint readout is natural
for this descended map.
-/

def mapSymbolicLatentPathHomotopyQuotient
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SymbolicLatentPathHomotopyQuotient (X := X) →
      SymbolicLatentPathHomotopyQuotient (X := Y) :=
  Quotient.lift
    (fun γ : SymbolicLatentPath X =>
      symbolicLatentPathHomotopyQuotientMap (f.comp γ))
    (by
      intro γ₀ γ₁ h
      apply Quotient.sound
      exact mapSymbolicLatentPathHomotopic f h)

@[simp] theorem mapSymbolicLatentPathHomotopyQuotient_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (γ : SymbolicLatentPath X) :
    mapSymbolicLatentPathHomotopyQuotient f
      (symbolicLatentPathHomotopyQuotientMap γ) =
        symbolicLatentPathHomotopyQuotientMap (f.comp γ) :=
  rfl

def mapSymbolicLatentPathHomotopyEndpoint
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : X × X → Y × Y :=
  fun p => (f p.1, f p.2)

theorem mapSymbolicLatentPathHomotopyQuotient_endpoint
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicLatentPathHomotopyQuotient f q) =
      mapSymbolicLatentPathHomotopyEndpoint f
        (symbolicLatentPathHomotopyEndpointMap q) := by
  refine Quotient.inductionOn q ?_
  intro γ
  rfl

theorem mapSymbolicLatentPathHomotopyQuotient_endpoint_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (mapSymbolicLatentPathHomotopyQuotient (g.comp f) q) =
      mapSymbolicLatentPathHomotopyEndpoint g
        (mapSymbolicLatentPathHomotopyEndpoint f
          (symbolicLatentPathHomotopyEndpointMap q)) := by
  simp [mapSymbolicLatentPathHomotopyEndpoint,
    mapSymbolicLatentPathHomotopyQuotient_endpoint]

theorem mapSymbolicLatentPathHomotopyQuotient_id
    {X : Type*} [TopologicalSpace X] :
    mapSymbolicLatentPathHomotopyQuotient
        (ContinuousMap.id X) = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro γ
  rfl

theorem mapSymbolicLatentPathHomotopyQuotient_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    mapSymbolicLatentPathHomotopyQuotient (g.comp f) =
      mapSymbolicLatentPathHomotopyQuotient g ∘
        mapSymbolicLatentPathHomotopyQuotient f := by
  funext q
  refine Quotient.inductionOn q ?_
  intro γ
  rfl

theorem mapSymbolicLatentPathHomotopyQuotient_comp_apply
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z))
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    mapSymbolicLatentPathHomotopyQuotient (g.comp f) q =
      (mapSymbolicLatentPathHomotopyQuotient g ∘
        mapSymbolicLatentPathHomotopyQuotient f) q := by
  exact congrArg (fun m => m q)
    (mapSymbolicLatentPathHomotopyQuotient_comp f g)

end InfoGeometry.Topology
