import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathPullbackCover

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` inclusions for pullbacks of symbolic-latent open covers

Each pullback domain is an open subspace of the path parameter interval (or of
the parameter-path product).  The cover itself remains the native finite
family from `SymbolicLatentOpenCover`; this file exposes its members as
categorical inclusions without introducing a new cover structure.
-/

def symbolicLatentPathPullbackDomainInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    {κ : Type} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (k : κ) :
    TopCat.of {t // t ∈ symbolicLatentPathPullbackDomain C γ k} ⟶
      TopCat.of SymbolicPathDomain :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentPathPullbackDomainInclusion_isOpenEmbedding
    {X : Type} [TopologicalSpace X]
    {κ : Type} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (k : κ) :
    Topology.IsOpenEmbedding
      (Subtype.val :
        {t // t ∈ symbolicLatentPathPullbackDomain C γ k} →
          SymbolicPathDomain) :=
  (isOpen_symbolicLatentPathPullbackDomain C γ k).isOpenEmbedding_subtypeVal

@[simp] theorem symbolicLatentPathPullbackDomainInclusionTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {κ : Type} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (γ : SymbolicLatentPath X) (k : κ)
    (t : {t // t ∈ symbolicLatentPathPullbackDomain C γ k}) :
    symbolicLatentPathPullbackDomainInclusionTopCatHom C γ k t = t.1 :=
  rfl

def symbolicLatentFamilyPullbackDomainInclusionTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {κ : Type} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (F : SymbolicLatentPathFamily P X) (k : κ) :
    TopCat.of {z // z ∈ symbolicLatentFamilyPullbackDomain C F k} ⟶
      TopCat.of (P × SymbolicPathDomain) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentFamilyPullbackDomainInclusion_isOpenEmbedding
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {κ : Type} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (F : SymbolicLatentPathFamily P X) (k : κ) :
    Topology.IsOpenEmbedding
      (Subtype.val :
        {z // z ∈ symbolicLatentFamilyPullbackDomain C F k} →
          P × SymbolicPathDomain) :=
  (isOpen_symbolicLatentFamilyPullbackDomain C F k).isOpenEmbedding_subtypeVal

@[simp] theorem symbolicLatentFamilyPullbackDomainInclusionTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {κ : Type} [Fintype κ]
    (C : SymbolicLatentOpenCover X κ)
    (F : SymbolicLatentPathFamily P X) (k : κ)
    (z : {z // z ∈ symbolicLatentFamilyPullbackDomain C F k}) :
    symbolicLatentFamilyPullbackDomainInclusionTopCatHom C F k z = z.1 :=
  rfl

end InfoGeometry.Topology
