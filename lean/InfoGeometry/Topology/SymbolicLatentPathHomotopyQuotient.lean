import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopyComposition

namespace InfoGeometry.Topology

/-!
# Endpoint readout on symbolic-latent path homotopy classes

The quotient is formed only from the proven endpoint-preserving homotopy
Setoid.  Its endpoint map is defined by quotient lifting, with well-definedness
coming from the native endpoint-invariance theorem.  No topology on the path
space is assumed here.
-/

abbrev SymbolicLatentPathHomotopyQuotient
    {X : Type*} [TopologicalSpace X] :=
  Quotient (symbolicLatentPathHomotopySetoid (X := X))

def symbolicLatentPathHomotopyQuotientMap
    {X : Type*} [TopologicalSpace X] :
    SymbolicLatentPath X → SymbolicLatentPathHomotopyQuotient (X := X) :=
  Quotient.mk' (s := symbolicLatentPathHomotopySetoid (X := X))

theorem symbolicLatentPathHomotopyQuotientMap_surjective
    {X : Type*} [TopologicalSpace X] :
    Function.Surjective (symbolicLatentPathHomotopyQuotientMap (X := X)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro γ
  exact ⟨γ, rfl⟩

def symbolicLatentPathHomotopyEndpointMap
    {X : Type*} [TopologicalSpace X] :
    SymbolicLatentPathHomotopyQuotient (X := X) → X × X :=
  Quotient.lift (s := symbolicLatentPathHomotopySetoid (X := X))
    (fun γ : SymbolicLatentPath X => γ.endpoints)
    (by
      intro γ₀ γ₁ h
      exact h.same_endpoints)

@[simp] theorem symbolicLatentPathHomotopyEndpointMap_mk
    {X : Type*} [TopologicalSpace X] (γ : SymbolicLatentPath X) :
    symbolicLatentPathHomotopyEndpointMap
      (symbolicLatentPathHomotopyQuotientMap γ) = γ.endpoints :=
  rfl

theorem symbolicLatentPathHomotopyEndpointMap_eq_of_homotopic
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    symbolicLatentPathHomotopyEndpointMap
      (symbolicLatentPathHomotopyQuotientMap γ₀) =
      symbolicLatentPathHomotopyEndpointMap
        (symbolicLatentPathHomotopyQuotientMap γ₁) := by
  simpa using h.same_endpoints

end InfoGeometry.Topology
