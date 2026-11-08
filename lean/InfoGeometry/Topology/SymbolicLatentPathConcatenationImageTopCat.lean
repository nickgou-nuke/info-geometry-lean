import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathConcatenationImage
import InfoGeometry.Topology.SymbolicLatentPathImageTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Categorical image invariant for canonical path concatenation

The canonical concatenation image is the union of the two input images.  The
existing set equality is promoted to an isomorphism of the corresponding
subtype objects in `TopCat`.
-/

abbrev canonicalSymbolicConcatenationImage
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :=
  {x // x ∈ Set.range (canonicalSymbolicConcatenation hend)}

abbrev symbolicConcatenationImageUnion
    {X : Type} [TopologicalSpace X]
    (γ₀ γ₁ : SymbolicLatentPath X) :=
  {x // x ∈ Set.range γ₀ ∪ Set.range γ₁}

def canonicalSymbolicConcatenationImageToUnionTopCatHom
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    TopCat.of (canonicalSymbolicConcatenationImage hend) ⟶
      TopCat.of (symbolicConcatenationImageUnion γ₀ γ₁) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, by
          rw [← canonicalSymbolicConcatenation_range_eq_union hend]
          exact y.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }

def symbolicConcatenationImageUnionToCanonicalTopCatHom
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    TopCat.of (symbolicConcatenationImageUnion γ₀ γ₁) ⟶
      TopCat.of (canonicalSymbolicConcatenationImage hend) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, by
          rw [canonicalSymbolicConcatenation_range_eq_union hend]
          exact y.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }

theorem canonicalSymbolicConcatenationImageToUnionTopCatHom_isIso
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    IsIso (canonicalSymbolicConcatenationImageToUnionTopCatHom hend) := by
  refine IsIso.mk ⟨symbolicConcatenationImageUnionToCanonicalTopCatHom hend,
    ?_, ?_⟩
  · apply TopCat.hom_ext
    ext y
    rfl
  · apply TopCat.hom_ext
    ext y
    rfl

def canonicalSymbolicConcatenationImageInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    TopCat.of (canonicalSymbolicConcatenationImage hend) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def symbolicConcatenationImageUnionInclusionTopCatHom
    {X : Type} [TopologicalSpace X]
    (γ₀ γ₁ : SymbolicLatentPath X) :
    TopCat.of (symbolicConcatenationImageUnion γ₀ γ₁) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem canonicalSymbolicConcatenationImage_inclusion_natural
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    canonicalSymbolicConcatenationImageToUnionTopCatHom hend ≫
        symbolicConcatenationImageUnionInclusionTopCatHom γ₀ γ₁ =
      canonicalSymbolicConcatenationImageInclusionTopCatHom hend := by
  ext y
  rfl

theorem canonicalSymbolicConcatenationImage_toUnion_unique
    {X : Type} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start)
    {u : TopCat.of (canonicalSymbolicConcatenationImage hend) ⟶
      TopCat.of (symbolicConcatenationImageUnion γ₀ γ₁)}
    (hu : u ≫ symbolicConcatenationImageUnionInclusionTopCatHom γ₀ γ₁ =
      canonicalSymbolicConcatenationImageInclusionTopCatHom hend) :
    u = canonicalSymbolicConcatenationImageToUnionTopCatHom hend := by
  apply TopCat.hom_ext
  ext y
  have hy := congrArg (fun m => m y) hu
  simpa [canonicalSymbolicConcatenationImageToUnionTopCatHom,
    symbolicConcatenationImageUnionInclusionTopCatHom,
    canonicalSymbolicConcatenationImageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hy

end InfoGeometry.Topology
