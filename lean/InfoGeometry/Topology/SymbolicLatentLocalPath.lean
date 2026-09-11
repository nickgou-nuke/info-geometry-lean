import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathPullbackCover
import InfoGeometry.Topology.SymbolicLatentPathImage

namespace InfoGeometry.Topology

/-!
Chart-local symbolic paths.  A cover only provides local candidates; this
structure records the additional proof that one path stays in one selected
chart domain for its whole parameter interval.
-/

abbrev SymbolicLatentLocalPath
    (X κ : Type*) [TopologicalSpace X] [Fintype κ]
    (C : SymbolicLatentOpenCover X κ) :=
  {p : κ × SymbolicLatentPath X //
    ∀ t : SymbolicPathDomain, p.2 t ∈ C.domain p.1}

namespace SymbolicLatentLocalPath

abbrev chart
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) : κ :=
  γ.1.1

abbrev path
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) : SymbolicLatentPath X :=
  γ.1.2

abbrev stays_in_chart
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    ∀ t : SymbolicPathDomain, γ.path t ∈ C.domain γ.chart :=
  γ.2

end SymbolicLatentLocalPath

def SymbolicLatentLocalPath.image
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) : Set X :=
  symbolicLatentPathImage γ.path

theorem SymbolicLatentLocalPath.image_subset_chart
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.image ⊆ C.domain γ.chart := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  exact γ.stays_in_chart t

theorem SymbolicLatentLocalPath.start_mem_chart
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.path.start ∈ C.domain γ.chart := by
  exact γ.stays_in_chart 0

theorem SymbolicLatentLocalPath.finish_mem_chart
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.path.finish ∈ C.domain γ.chart := by
  exact γ.stays_in_chart 1

theorem SymbolicLatentLocalPath.image_isCompact
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    IsCompact γ.image :=
  isCompact_symbolicLatentPathImage γ.path

def SymbolicLatentLocalPath.pullbackDomain
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) : Set SymbolicPathDomain :=
  symbolicLatentPathPullbackDomain C γ.path γ.chart

theorem SymbolicLatentLocalPath.pullbackDomain_eq_univ
    {X κ : Type*} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.pullbackDomain = Set.univ := by
  ext t
  exact ⟨fun _ => trivial, fun _ => γ.stays_in_chart t⟩

end InfoGeometry.Topology
