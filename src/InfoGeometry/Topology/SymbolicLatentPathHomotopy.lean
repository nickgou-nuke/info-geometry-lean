import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

namespace InfoGeometry.Topology

/-!
Endpoint-preserving homotopies of symbolic latent paths.

The definition is intentionally purely topological.  It does not use the
octonion multiplication, a connection, or a differential.  Such structures
can act on this layer only after a continuous action has been supplied.
-/

abbrev SymbolicPathSquare :=
  SymbolicPathDomain × SymbolicPathDomain

structure SymbolicLatentPathHomotopy
    {X : Type*} [TopologicalSpace X]
    (γ₀ γ₁ : SymbolicLatentPath X) where
  map : C(SymbolicPathSquare, X)
  at_start : ∀ t : SymbolicPathDomain,
    map (0, t) = γ₀ t
  at_finish : ∀ t : SymbolicPathDomain,
    map (1, t) = γ₁ t
  fixed_start : ∀ s : SymbolicPathDomain,
    map (s, 0) = γ₀.start
  fixed_finish : ∀ s : SymbolicPathDomain,
    map (s, 1) = γ₀.finish

@[ext] theorem SymbolicLatentPathHomotopy.ext
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    {H K : SymbolicLatentPathHomotopy γ₀ γ₁}
    (hmap : H.map = K.map) :
    H = K := by
  cases H
  cases K
  cases hmap
  rfl

def SymbolicLatentPathHomotopic
    {X : Type*} [TopologicalSpace X]
    (γ₀ γ₁ : SymbolicLatentPath X) : Prop :=
  Nonempty (SymbolicLatentPathHomotopy γ₀ γ₁)

theorem SymbolicLatentPathHomotopy.same_start
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    γ₀.start = γ₁.start := by
  change γ₀ 0 = γ₁ 0
  exact (H.at_start 0).symm.trans <|
    (H.fixed_start 0).trans <|
      (H.fixed_start 1).symm.trans (H.at_finish 0)

theorem SymbolicLatentPathHomotopy.same_finish
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    γ₀.finish = γ₁.finish := by
  change γ₀ 1 = γ₁ 1
  exact (H.at_start 1).symm.trans <|
    (H.fixed_finish 0).trans <|
      (H.fixed_finish 1).symm.trans (H.at_finish 1)

theorem SymbolicLatentPathHomotopic.same_endpoints
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    γ₀.endpoints = γ₁.endpoints := by
  rcases h with ⟨H⟩
  exact Prod.ext H.same_start H.same_finish

def SymbolicLatentPathEndpointClass
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) : Set (X × X) :=
  {q | q = γ.endpoints}

theorem mem_SymbolicLatentPathEndpointClass
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    γ.endpoints ∈ SymbolicLatentPathEndpointClass γ := by
  rfl

theorem SymbolicLatentPathHomotopic.same_endpoint_class
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    SymbolicLatentPathEndpointClass γ₀ =
      SymbolicLatentPathEndpointClass γ₁ := by
  have hend : γ₀.endpoints = γ₁.endpoints := h.same_endpoints
  simp [SymbolicLatentPathEndpointClass, hend]

end InfoGeometry.Topology
