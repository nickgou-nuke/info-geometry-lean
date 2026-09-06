import Mathlib
import InfoGeometry.Topology.SymbolicLatentLoop

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` inclusion for symbolic-latent loops

The loop predicate is a subtype condition on the path space.  This owner
packages the loop carrier as a topological subspace and exposes the canonical
inclusion into the path space.
-/

abbrev SymbolicLatentLoopSpace
    {X : Type*} [TopologicalSpace X] :=
  {γ : SymbolicLatentPath X // SymbolicLatentLoop (X := X) γ}

def symbolicLatentLoopInclusionTopCatHom
    {X : Type*} [TopologicalSpace X] :
    TopCat.of (SymbolicLatentLoopSpace (X := X)) ⟶
      TopCat.of (SymbolicLatentPath X) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentLoopInclusionTopCatHom_apply
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentLoopSpace (X := X)) :
    symbolicLatentLoopInclusionTopCatHom (X := X) γ = γ.1 :=
  rfl

def constantSymbolicLatentLoopSpace
    {X : Type*} [TopologicalSpace X] (x : X) :
    SymbolicLatentLoopSpace (X := X) :=
  ⟨constantSymbolicLatentPath x, constantSymbolicLatentPath_isLoop x⟩

theorem constantSymbolicLatentLoopSpace_apply
    {X : Type*} [TopologicalSpace X] (x : X) :
    (constantSymbolicLatentLoopSpace (X := X) x).1 =
      constantSymbolicLatentPath x :=
  rfl

def reverseSymbolicLatentLoopSpace
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentLoopSpace (X := X)) :
    SymbolicLatentLoopSpace (X := X) :=
  ⟨reverseSymbolicLatentPath γ.1,
    reverseSymbolicLatentPath_isLoop γ.2⟩

theorem reverseSymbolicLatentLoopSpace_apply
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentLoopSpace (X := X)) :
    (reverseSymbolicLatentLoopSpace (X := X) γ).1 =
      reverseSymbolicLatentPath γ.1 :=
  rfl

end InfoGeometry.Topology
