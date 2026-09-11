import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBasedLoopPath
import InfoGeometry.Topology.SymbolicLatentPathFunctoriality
import InfoGeometry.Topology.SymbolicLatentBasedLoopPathFunctoriality

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` inclusion for symbolic-latent based loops

The based-loop carrier is a subtype of the path space.  This file exposes the
canonical inclusion as a `TopCat` morphism without claiming any new quotient
or group structure.
-/

def symbolicLatentBasedLoopPathInclusionTopCatHom
    {X : Type} [TopologicalSpace X] {x : X} :
    TopCat.of (SymbolicLatentBasedLoopPath x) ⟶
      TopCat.of (SymbolicLatentPath X) :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem symbolicLatentBasedLoopPathInclusionTopCatHom_apply
    {X : Type} [TopologicalSpace X] {x : X}
    (γ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopPathInclusionTopCatHom (x := x) γ =
      γ.1 :=
  rfl

theorem canonicalSymbolicLatentBasedLoopConcatenation_inclusion
    {X : Type} [TopologicalSpace X] {x : X}
    (γ₀ γ₁ : SymbolicLatentBasedLoopPath x) :
    symbolicLatentBasedLoopPathInclusionTopCatHom (x := x)
        (canonicalSymbolicLatentBasedLoopConcatenation γ₀ γ₁) =
      canonicalSymbolicConcatenation
        (γ₀.2.2.trans γ₁.2.1.symm) := by
  rfl

theorem symbolicLatentBasedLoopPathInclusionTopCatHom_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f)
    {x : X} {y : Y} (hxy : f x = y) :
    symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
        symbolicLatentBasedLoopPathInclusionTopCatHom (x := y) =
      symbolicLatentBasedLoopPathInclusionTopCatHom (x := x) ≫
        symbolicLatentPathTopCatHom f hf := by
  ext γ t
  rfl

theorem symbolicLatentBasedLoopPathInclusionTopCatHom_natural_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
        symbolicLatentBasedLoopPathTopCatHom ⟨g, hg⟩ hyz ≫
        symbolicLatentBasedLoopPathInclusionTopCatHom (x := z) =
      symbolicLatentBasedLoopPathInclusionTopCatHom (x := x) ≫
        symbolicLatentPathTopCatHom f hf ≫
        symbolicLatentPathTopCatHom g hg := by
  calc
    symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
        symbolicLatentBasedLoopPathTopCatHom ⟨g, hg⟩ hyz ≫
        symbolicLatentBasedLoopPathInclusionTopCatHom (x := z)
      = symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
          (symbolicLatentBasedLoopPathTopCatHom ⟨g, hg⟩ hyz ≫
            symbolicLatentBasedLoopPathInclusionTopCatHom (x := z)) := by
          simp
    _ = symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
          (symbolicLatentBasedLoopPathInclusionTopCatHom (x := y) ≫
            symbolicLatentPathTopCatHom g hg) := by
          rw [symbolicLatentBasedLoopPathInclusionTopCatHom_natural
            (f := g) (hf := hg) (hxy := hyz)]
    _ = (symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
          symbolicLatentBasedLoopPathInclusionTopCatHom (x := y)) ≫
          symbolicLatentPathTopCatHom g hg := by
          simp [Category.assoc]
    _ = (symbolicLatentBasedLoopPathInclusionTopCatHom (x := x) ≫
          symbolicLatentPathTopCatHom f hf) ≫
          symbolicLatentPathTopCatHom g hg := by
          rw [symbolicLatentBasedLoopPathInclusionTopCatHom_natural
            (f := f) (hf := hf) (hxy := hxy)]
    _ = symbolicLatentBasedLoopPathInclusionTopCatHom (x := x) ≫
          symbolicLatentPathTopCatHom f hf ≫
          symbolicLatentPathTopCatHom g hg := by
          simp

theorem symbolicLatentBasedLoopPathTopCatHom_comp_base
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z) :
    symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
        symbolicLatentBasedLoopPathTopCatHom ⟨g, hg⟩ hyz =
      symbolicLatentBasedLoopPathTopCatHom ⟨g.comp f, hg.comp hf⟩
        ((congrArg g hxy).trans hyz) := by
  ext γ t
  exact congrArg (fun p => p.1 t)
    (mapSymbolicLatentBasedLoopPath_comp
      (⟨f, hf⟩) (⟨g, hg⟩) hxy hyz γ)

theorem symbolicLatentBasedLoopPathTopCatHom_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    {x : X} {y : Y} {z : Z}
    (hxy : f x = y) (hyz : g y = z)
    (γ : SymbolicLatentBasedLoopPath x) :
    (symbolicLatentBasedLoopPathTopCatHom ⟨f, hf⟩ hxy ≫
        symbolicLatentBasedLoopPathTopCatHom ⟨g, hg⟩ hyz) γ =
      symbolicLatentBasedLoopPathTopCatHom ⟨g.comp f, hg.comp hf⟩
        ((congrArg g hxy).trans hyz) γ := by
  exact congrArg (fun m => m γ)
    (symbolicLatentBasedLoopPathTopCatHom_comp_base
      (f := f) (g := g) (hf := hf) (hg := hg) (hxy := hxy) (hyz := hyz))

end InfoGeometry.Topology
