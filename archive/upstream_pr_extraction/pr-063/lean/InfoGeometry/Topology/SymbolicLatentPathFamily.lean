import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathEndpoints

namespace InfoGeometry.Topology

/-!
Jointly continuous families of symbolic latent paths.  The family parameter
is kept abstract; this is the topological interface needed before adding
local charts, flows, or homotopy reparametrisations.
-/

abbrev SymbolicLatentPathFamily
    (P X : Type*) [TopologicalSpace P] [TopologicalSpace X] :=
  C(P × SymbolicPathDomain, X)

def SymbolicLatentPathFamily.slice
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P) :
    SymbolicLatentPath X := {
  toFun := fun t => F (p, t)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
}

theorem SymbolicLatentPathFamily.slice_apply
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P)
    (t : SymbolicPathDomain) :
    F.slice p t = F (p, t) := rfl

def SymbolicLatentPathFamily.startFamily
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) : C(P, X) := {
  toFun := fun p => F (p, 0)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
}

def SymbolicLatentPathFamily.finishFamily
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) : C(P, X) := {
  toFun := fun p => F (p, 1)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
}

theorem SymbolicLatentPathFamily.startFamily_apply
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P) :
    F.startFamily p = (F.slice p).start := rfl

theorem SymbolicLatentPathFamily.finishFamily_apply
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (p : P) :
    F.finishFamily p = (F.slice p).finish := rfl

theorem SymbolicLatentPathFamily.startFamily_continuous
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) :
    Continuous F.startFamily :=
  F.startFamily.continuous

theorem SymbolicLatentPathFamily.finishFamily_continuous
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) :
    Continuous F.finishFamily :=
  F.finishFamily.continuous

def SymbolicLatentPathFamily.InRegion
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) (R : Set X) : Prop :=
  ∀ p : P, ∀ t : SymbolicPathDomain, F (p, t) ∈ R

theorem SymbolicLatentPathFamily.slice_inRegion
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {F : SymbolicLatentPathFamily P X} {R : Set X}
    (hF : F.InRegion R) (p : P) :
    ∀ t : SymbolicPathDomain, F.slice p t ∈ R := by
  intro t
  exact hF p t

theorem SymbolicLatentPathFamily.startFamily_mem
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {F : SymbolicLatentPathFamily P X} {R : Set X}
    (hF : F.InRegion R) (p : P) :
    F.startFamily p ∈ R := by
  exact hF p 0

theorem SymbolicLatentPathFamily.finishFamily_mem
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {F : SymbolicLatentPathFamily P X} {R : Set X}
    (hF : F.InRegion R) (p : P) :
    F.finishFamily p ∈ R := by
  exact hF p 1

def symbolicLatentPathFamilyImage
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : SymbolicLatentPathFamily P X) : Set X :=
  Set.range F

theorem isCompact_symbolicLatentPathFamilyImage
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P]
    (F : SymbolicLatentPathFamily P X) :
    IsCompact (symbolicLatentPathFamilyImage F) := by
  exact isCompact_range F.continuous

theorem symbolicLatentPathFamilyImage_subset
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {F : SymbolicLatentPathFamily P X} {R : Set X}
    (hF : F.InRegion R) :
  symbolicLatentPathFamilyImage F ⊆ R := by
  intro x hx
  rcases hx with ⟨⟨p, t⟩, rfl⟩
  exact hF p t

end InfoGeometry.Topology
