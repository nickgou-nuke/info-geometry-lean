import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamily

namespace InfoGeometry.Topology

/-!
Pullback of a finite open cover along a symbolic latent path.  This is the
topological interface for changing local latent charts along a trajectory.
-/

structure SymbolicLatentOpenCover
    (X κ : Type*) [TopologicalSpace X] [Fintype κ] where
  domain : κ → Set X
  isOpen_domain : ∀ k, IsOpen (domain k)
  covers : ∀ x : X, ∃ k, x ∈ domain k

def symbolicLatentPathPullbackDomain
    {X : Type*} [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (k : κ) : Set SymbolicPathDomain :=
  γ ⁻¹' C.domain k

theorem isOpen_symbolicLatentPathPullbackDomain
    {X : Type*} [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (k : κ) :
    IsOpen (symbolicLatentPathPullbackDomain C γ k) := by
  exact (C.isOpen_domain k).preimage γ.continuous

theorem symbolicLatentPathPullbackDomain_covers
    {X : Type*} [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    ∃ k, t ∈ symbolicLatentPathPullbackDomain C γ k := by
  rcases C.covers (γ t) with ⟨k, hk⟩
  exact ⟨k, hk⟩

def symbolicLatentPathPullbackIndexSet
    {X : Type*} [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) : Set κ :=
  {k | t ∈ symbolicLatentPathPullbackDomain C γ k}

theorem symbolicLatentPathPullbackIndexSet_nonempty
    {X : Type*} [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (t : SymbolicPathDomain) :
    (symbolicLatentPathPullbackIndexSet C γ t).Nonempty := by
  rcases symbolicLatentPathPullbackDomain_covers C γ t with ⟨k, hk⟩
  exact ⟨k, hk⟩

def symbolicLatentFamilyPullbackDomain
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (F : SymbolicLatentPathFamily P X) (k : κ) :
    Set (P × SymbolicPathDomain) :=
  F ⁻¹' C.domain k

theorem isOpen_symbolicLatentFamilyPullbackDomain
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (F : SymbolicLatentPathFamily P X) (k : κ) :
    IsOpen (symbolicLatentFamilyPullbackDomain C F k) := by
  exact (C.isOpen_domain k).preimage F.continuous

theorem symbolicLatentFamilyPullbackDomain_covers
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {κ : Type*} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (F : SymbolicLatentPathFamily P X)
    (p : P) (t : SymbolicPathDomain) :
    ∃ k, (p, t) ∈ symbolicLatentFamilyPullbackDomain C F k := by
  rcases C.covers (F (p, t)) with ⟨k, hk⟩
  exact ⟨k, hk⟩

end InfoGeometry.Topology
