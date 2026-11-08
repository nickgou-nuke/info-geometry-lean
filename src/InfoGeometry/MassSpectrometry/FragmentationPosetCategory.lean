import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.FragmentationDAG

/-!
# Fragmentation reachability as a preorder category

The repository already uses the native Mathlib preorder-category construction
for ranked causal nets.  This module gives `FragmentationDAG` the same
categorical interface: objects are fragments and there is a unique arrow
whenever the target is reachable from the source.

This is an indexing category for fragmentation diagrams.  It does not by
itself assert that any particular molecular reconstruction is a colimit.
-/

namespace InfoGeometry.MassSpectrometry

open CategoryTheory

namespace FragmentationDAG

variable {n : ℕ} (D : FragmentationDAG n)

/-- Reachability induces the canonical causal preorder. -/
def reachPreorder : Preorder (Fin n) :=
  { le := D.Reach
    lt := fun source target => D.Reach source target ∧ ¬ D.Reach target source
    le_refl := by
      intro a
      exact Relation.ReflTransGen.refl
    le_trans := by
      intro a b c hab hbc
      exact Relation.ReflTransGen.trans hab hbc
    lt_iff_le_not_ge := by
      intro a b
      rfl }

/-- Causal arrows in the induced preorder category are exactly reachable
fragment pairs. -/
theorem hom_iff_reach (source target : Fin n) :
    (letI : Preorder (Fin n) := D.reachPreorder
      ; Nonempty (source ⟶ target)) ↔
    D.Reach source target := by
  letI : Preorder (Fin n) := D.reachPreorder
  constructor
  · rintro ⟨f⟩
    exact leOfHom f
  · intro h
    exact ⟨homOfLE h⟩

/-- Every physical fragmentation edge gives a causal arrow. -/
theorem edge_hom {source target : Fin n} (h : D.edge source target) :
    (letI : Preorder (Fin n) := D.reachPreorder
      ; Nonempty (source ⟶ target)) := by
  letI : Preorder (Fin n) := D.reachPreorder
  exact ⟨homOfLE (Relation.ReflTransGen.single h)⟩

/-- Every nonempty fragmentation path gives a causal arrow. -/
theorem strictReach_hom {source target : Fin n}
    (h : D.StrictReach source target) :
    (letI : Preorder (Fin n) := D.reachPreorder
      ; Nonempty (source ⟶ target)) := by
  letI : Preorder (Fin n) := D.reachPreorder
  exact ⟨homOfLE h.to_reflTransGen⟩

/-- Along a strict categorical fragmentation arrow witnessed by a nonempty
path, rank strictly decreases. -/
theorem strictReach_rank_decreases {source target : Fin n}
    (h : D.StrictReach source target) :
    D.rank target < D.rank source :=
  D.transGen_rank_lt h

end FragmentationDAG

end InfoGeometry.MassSpectrometry
