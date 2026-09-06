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
noncomputable def VertexPushout (S : MolecularFragmentSpan k nLeft nRight) : Type :=
  pushout S.toLeft.toFun S.toRight.toFun

/-- Left fragment injection into the reconstructed carrier. -/
noncomputable def inLeft (S : MolecularFragmentSpan k nLeft nRight) :
    Fin nLeft → S.VertexPushout :=
  pushout.inl S.toLeft.toFun S.toRight.toFun

/-- Right fragment injection into the reconstructed carrier. -/
noncomputable def inRight (S : MolecularFragmentSpan k nLeft nRight) :
    Fin nRight → S.VertexPushout :=
  pushout.inr S.toLeft.toFun S.toRight.toFun

/-- Shared atoms are identified by the pushout. -/
@[simp] theorem shared_glue (S : MolecularFragmentSpan k nLeft nRight)
    (i : Fin k) :
    S.inLeft (S.toLeft.toFun i) = S.inRight (S.toRight.toFun i) := by
  exact congrFun
    (pushout.condition (f := S.toLeft.toFun) (g := S.toRight.toFun)) i

/-- Atom labels descend to the pushout carrier. -/
noncomputable def atomLabel (S : MolecularFragmentSpan k nLeft nRight) :
    S.VertexPushout → AtomLabel :=
  pushout.desc S.left.atom S.right.atom (by
    change (S.toLeft.toFun : Fin k ⟶ Fin nLeft) ≫
        (S.left.atom : Fin nLeft ⟶ AtomLabel) =
      (S.toRight.toFun : Fin k ⟶ Fin nRight) ≫
        (S.right.atom : Fin nRight ⟶ AtomLabel)
    ext i
    exact (S.toLeft.atom_preserving i).trans
      (S.toRight.atom_preserving i).symm)

@[simp] theorem atomLabel_inLeft
    (S : MolecularFragmentSpan k nLeft nRight) (i : Fin nLeft) :
    S.atomLabel (S.inLeft i) = S.left.atom i := by
  exact congrFun (pushout.inl_desc _ _ _) i

@[simp] theorem atomLabel_inRight
    (S : MolecularFragmentSpan k nLeft nRight) (i : Fin nRight) :
    S.atomLabel (S.inRight i) = S.right.atom i := by
  exact congrFun (pushout.inr_desc _ _ _) i

/-- Universal lift from compatible fragment maps. -/
noncomputable def lift (S : MolecularFragmentSpan k nLeft nRight)
    {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i)) :
    S.VertexPushout → X :=
  pushout.desc u v (by
    change (S.toLeft.toFun : Fin k ⟶ Fin nLeft) ≫ (u : Fin nLeft ⟶ X) =
      (S.toRight.toFun : Fin k ⟶ Fin nRight) ≫ (v : Fin nRight ⟶ X)
    ext i
    exact h i)

@[simp] theorem lift_inLeft
    (S : MolecularFragmentSpan k nLeft nRight)
    {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i))
    (x : Fin nLeft) :
    S.lift u v h (S.inLeft x) = u x := by
  exact congrFun (pushout.inl_desc u v (by
    change (S.toLeft.toFun : Fin k ⟶ Fin nLeft) ≫ (u : Fin nLeft ⟶ X) =
      (S.toRight.toFun : Fin k ⟶ Fin nRight) ≫ (v : Fin nRight ⟶ X)
    ext i
    exact h i)) x

@[simp] theorem lift_inRight
    (S : MolecularFragmentSpan k nLeft nRight)
    {X : Type} (u : Fin nLeft → X) (v : Fin nRight → X)
    (h : ∀ i : Fin k, u (S.toLeft.toFun i) = v (S.toRight.toFun i))
    (x : Fin nRight) :
    S.lift u v h (S.inRight x) = v x := by
  exact congrFun (pushout.inr_desc u v (by
    change (S.toLeft.toFun : Fin k ⟶ Fin nLeft) ≫ (u : Fin nLeft ⟶ X) =
      (S.toRight.toFun : Fin k ⟶ Fin nRight) ≫ (v : Fin nRight ⟶ X)
    ext i
    exact h i)) x

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
  have hL :
      pushout.inl S.toLeft.toFun S.toRight.toFun ≫ w =
        pushout.inl S.toLeft.toFun S.toRight.toFun ≫ S.lift u v h := by
    ext x
    rw [hwLeft x, S.lift_inLeft u v h x]
  have hR :
      pushout.inr S.toLeft.toFun S.toRight.toFun ≫ w =
        pushout.inr S.toLeft.toFun S.toRight.toFun ≫ S.lift u v h := by
    ext x
    rw [hwRight x, S.lift_inRight u v h x]
  exact congrFun (pushout.hom_ext hL hR) z

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
