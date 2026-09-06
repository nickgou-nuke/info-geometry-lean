import Mathlib
import InfoGeometry.MassSpectrometry.ChemicalGraph

/-!
# Molecular fragment pushout reconstruction

This module gives fragment gluing a genuine categorical universal property.
The pushout is taken in `Type` over exact molecular-graph embeddings.  Atom
labels descend canonically because the embeddings preserve labels.

The induced bond predicate below is the union of the two fragment bond images.
We do not claim that this is a pushout in a category of labelled graphs: that
stronger statement requires a dedicated graph-category owner.  What is proved
here is the exact vertex/atom colimit and its universal mapping property.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open CategoryTheory CategoryTheory.Limits

/-- A cospan of two molecular fragments over a shared exact subgraph. -/
structure MolecularFragmentSpan (k nLeft nRight : ℕ) where
  shared : MolecularGraph k
  left : MolecularGraph nLeft
  right : MolecularGraph nRight
  toLeft : shared.Embedding left
  toRight : shared.Embedding right

namespace MolecularFragmentSpan

variable {k nLeft nRight : ℕ}

/-- Categorical vertex pushout of the two fragment embeddings. -/
abbrev VertexPushout (S : MolecularFragmentSpan k nLeft nRight) : Type :=
  CategoryTheory.Limits.Types.Pushout
    (CategoryTheory.ConcreteCategory.ofHom S.toLeft.toFun)
    (CategoryTheory.ConcreteCategory.ofHom S.toRight.toFun)

/-- Left fragment injection into the reconstructed carrier. -/
noncomputable def inLeft (S : MolecularFragmentSpan k nLeft nRight) :
    Fin nLeft ⟶ S.VertexPushout :=
  CategoryTheory.Limits.Types.Pushout.inl
    (CategoryTheory.ConcreteCategory.ofHom S.toLeft.toFun)
    (CategoryTheory.ConcreteCategory.ofHom S.toRight.toFun)

/-- Right fragment injection into the reconstructed carrier. -/
noncomputable def inRight (S : MolecularFragmentSpan k nLeft nRight) :
    Fin nRight ⟶ S.VertexPushout :=
  CategoryTheory.Limits.Types.Pushout.inr
    (CategoryTheory.ConcreteCategory.ofHom S.toLeft.toFun)
    (CategoryTheory.ConcreteCategory.ofHom S.toRight.toFun)

/-- Shared atoms are identified by the pushout. -/
@[simp] theorem shared_glue (S : MolecularFragmentSpan k nLeft nRight)
    (i : Fin k) :
    S.inLeft (S.toLeft.toFun i) = S.inRight (S.toRight.toFun i) := by
  have h := CategoryTheory.Limits.Types.Pushout.condition
    (CategoryTheory.ConcreteCategory.ofHom S.toLeft.toFun)
    (CategoryTheory.ConcreteCategory.ofHom S.toRight.toFun)
  exact CategoryTheory.ConcreteCategory.congr_hom h i

/-- Atom labels descend to the pushout carrier. -/
noncomputable def atomLabel (S : MolecularFragmentSpan k nLeft nRight) :
    S.VertexPushout → AtomLabel :=
  let f : Fin k ⟶ Fin nLeft := S.toLeft.toFun
  let g : Fin k ⟶ Fin nRight := S.toRight.toFun
  let c : PushoutCocone f g := PushoutCocone.mk
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) S.left.atom)
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) S.right.atom) (by
      apply CategoryTheory.ConcreteCategory.ext_apply
      intro i
      simpa only [CategoryTheory.types_comp_apply] using (S.toLeft.atom_preserving i).trans
        (S.toRight.atom_preserving i).symm)
  CategoryTheory.ConcreteCategory.hom
    ((CategoryTheory.Limits.Types.Pushout.isColimitCocone f g).desc c)

@[simp] theorem atomLabel_inLeft
    (S : MolecularFragmentSpan k nLeft nRight) (i : Fin nLeft) :
    S.atomLabel (S.inLeft i) = S.left.atom i := by
  let f : Fin k ⟶ Fin nLeft := S.toLeft.toFun
  let g : Fin k ⟶ Fin nRight := S.toRight.toFun
  let c : PushoutCocone f g := PushoutCocone.mk
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) S.left.atom)
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) S.right.atom)
    (by apply CategoryTheory.ConcreteCategory.ext_apply; intro j
        simpa only [CategoryTheory.types_comp_apply] using (S.toLeft.atom_preserving j).trans
          (S.toRight.atom_preserving j).symm)
  exact CategoryTheory.ConcreteCategory.congr_hom
    ((CategoryTheory.Limits.Types.Pushout.isColimitCocone f g).fac c WalkingCospan.left) i

@[simp] theorem atomLabel_inRight
    (S : MolecularFragmentSpan k nLeft nRight) (i : Fin nRight) :
    S.atomLabel (S.inRight i) = S.right.atom i := by
  let f : Fin k ⟶ Fin nLeft := S.toLeft.toFun
  let g : Fin k ⟶ Fin nRight := S.toRight.toFun
  let c : PushoutCocone f g := PushoutCocone.mk
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) S.left.atom)
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) S.right.atom)
    (by apply CategoryTheory.ConcreteCategory.ext_apply; intro j
        simpa only [CategoryTheory.types_comp_apply] using (S.toLeft.atom_preserving j).trans
          (S.toRight.atom_preserving j).symm)
  exact CategoryTheory.ConcreteCategory.congr_hom
    ((CategoryTheory.Limits.Types.Pushout.isColimitCocone f g).fac c WalkingCospan.right) i

/-- Universal lift from compatible fragment maps. -/
noncomputable def lift (S : MolecularFragmentSpan k nLeft nRight)
  {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i)) :
  S.VertexPushout → X :=
  let f : Fin k ⟶ Fin nLeft := S.toLeft.toFun
  let g : Fin k ⟶ Fin nRight := S.toRight.toFun
  let c : PushoutCocone f g := PushoutCocone.mk
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) u)
    (CategoryTheory.ConcreteCategory.ofHom (C := Type) v) (by
    apply CategoryTheory.ConcreteCategory.ext_apply
    intro i
    exact h i)
  CategoryTheory.ConcreteCategory.hom
    ((CategoryTheory.Limits.Types.Pushout.isColimitCocone f g).desc c)

@[simp] theorem lift_inLeft
    (S : MolecularFragmentSpan k nLeft nRight)
    {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i))
    (x : Fin nLeft) :
    S.lift u v h (S.inLeft x) = u x := by
  rfl

@[simp] theorem lift_inRight
    (S : MolecularFragmentSpan k nLeft nRight)
    {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i))
    (x : Fin nRight) :
    S.lift u v h (S.inRight x) = v x := by
  rfl

/-- Uniqueness part of the pushout universal property. -/
theorem lift_unique
    (S : MolecularFragmentSpan k nLeft nRight)
    {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i))
    (w : S.VertexPushout → X)
    (hwLeft : ∀ x, w (S.inLeft x) = u x)
    (hwRight : ∀ x, w (S.inRight x) = v x) :
    w = S.lift u v h := by
  funext z
  refine Quot.inductionOn z ?_
  intro z
  cases z with
  | inl x =>
      change w (S.inLeft x) = S.lift u v h (S.inLeft x)
      rw [hwLeft x, S.lift_inLeft u v h x]
  | inr x =>
      change w (S.inRight x) = S.lift u v h (S.inRight x)
      rw [hwRight x, S.lift_inRight u v h x]

/-- Bond relation inherited from either fragment image. -/
def Bonded (S : MolecularFragmentSpan k nLeft nRight)
    (x y : S.VertexPushout) : Prop :=
  (∃ i j : Fin nLeft,
      x = S.inLeft i ∧ y = S.inLeft j ∧ S.left.Adj i j) ∨
  (∃ i j : Fin nRight,
      x = S.inRight i ∧ y = S.inRight j ∧ S.right.Adj i j)

/-- The inherited bond relation is symmetric. -/
theorem bonded_symm (S : MolecularFragmentSpan k nLeft nRight)
    {x y : S.VertexPushout} : S.Bonded x y → S.Bonded y x := by
  intro h
  rcases h with hL | hR
  · rcases hL with ⟨i, j, hx, hy, hij⟩
    left
    refine ⟨j, i, hy, hx, ?_⟩
    exact (S.left.adj_symm).mpr hij
  · rcases hR with ⟨i, j, hx, hy, hij⟩
    right
    refine ⟨j, i, hy, hx, ?_⟩
    exact (S.right.adj_symm).mpr hij

end MolecularFragmentSpan

end InfoGeometry.MassSpectrometry
