import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Presentable.Finite

open CategoryTheory
open CategoryTheory.Limits
open SSet
open Opposite

universe u

-- We formalize Nick Rozenblyum's Lemma on Filtered Colimits of ∞-Categories
-- Specifically, mapping spaces commute with filtered colimits for compact objects.

-- Let J be a filtered category.
-- Let F : J ⥤ SSet be a filtered diagram of simplicial sets (which model ∞-categories).
-- Let c be a compact object (finitely presentable simplicial set).

-- The structural isomorphism `Maps(c, colim d_i) ≃ colim Maps(c, d_i)` is formulated
-- as the preservation of filtered colimits by the corepresentable functor `Maps(c, -)`.

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable (F : J ⥤ SSet.{u}) (c : SSet.{u})

/-- A compact object in the ∞-category setting is exactly a finitely presentable object.
    For such objects, the mapping space functor `Maps(c, -)` commutes with filtered colimits. -/
noncomputable def rozenblyum_mapping_space_commutes_colimit
    [IsFinitelyPresentable c] [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op c))] :
    (c ⟶ colimit F) ≅ colimit (F ⋙ coyoneda.obj (op c)) := by
  haveI : PreservesFilteredColimits (coyoneda.obj (op c)) :=
    isFinitelyPresentable_iff_preservesFilteredColimits.mp ‹IsFinitelyPresentable c›
  haveI : PreservesColimitsOfShape J (coyoneda.obj (op c)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  exact preservesColimitIso (coyoneda.obj (op c)) F
