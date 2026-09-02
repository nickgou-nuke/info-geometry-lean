import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Types

/-!
# Categorical colimit of filtered braid-group stages

The repository already contains finite presented braid groups, finite-generator
and word colimits, and colimits of carriers carrying braid actions. This file
supplies the missing group-level categorical object: a filtered diagram in
Grp, its universal colimit, descent of compatible Artin generator
endomorphisms, and descent of compatible stage representations.

No claim is made that the finite-stage diagram is canonical until an explicit
functor B : ℕ ⥤ Grp is supplied. This keeps the transition homomorphisms
visible and prevents confusing a generator-index boundary with a colimit of
groups.
-/

noncomputable section

namespace InfoGeometry.Categorical.HadjiivanovBraidGroupColimit

open CategoryTheory
open CategoryTheory.Limits

universe u

/-- A filtered diagram of finite braid-group stages. -/
abbrev BraidGroupDiagram := ℕ ⥤ Grp.{u}

/-- Explicit finite-stage braid-group tower data.  The bonding maps are
part of the datum so the combinatorial straight-strand proof can be supplied
by the presentation owner without changing the categorical API. -/
structure BraidGroupTower where
  stage : ℕ → Grp.{u}
  bond : ∀ n : ℕ, stage n ⟶ stage (n + 1)

/-- The sequential category-theoretic diagram associated with a braid-group
 tower. -/
def BraidGroupTower.diagram (T : BraidGroupTower.{u}) : BraidGroupDiagram.{u} :=
  Functor.ofSequence T.bond

/-- The genuine categorical colimit of a supplied braid-group diagram. -/
abbrev BraidGroupColimit (B : BraidGroupDiagram.{u}) : Grp.{u} :=
  colimit B

/-- The canonical inclusion of the nth braid-group stage into the colimit. -/
abbrev stageInjection (B : BraidGroupDiagram.{u}) (n : ℕ) :
    B.obj n ⟶ BraidGroupColimit B :=
  colimit.ι B n

/-- A compatible pair of Artin generator endomorphisms on a filtered
braid-group diagram. -/
structure ArtinNaturalData (B : BraidGroupDiagram.{u}) where
  braid1 : B ⟶ B
  braid2 : B ⟶ B
  artin : ∀ n : ℕ,
    braid1.app n ≫ braid2.app n ≫ braid1.app n =
      braid2.app n ≫ braid1.app n ≫ braid2.app n

/-- The endomorphism of the braid-group colimit induced by a natural
endomorphism of the finite-stage diagram. -/
abbrev descendedEndomorphism
    (B : BraidGroupDiagram.{u}) (η : B ⟶ B) :
    BraidGroupColimit B ⟶ BraidGroupColimit B :=
  colim.map η

/-- The universal stage equation for a descended braid endomorphism. -/
theorem stageInjection_descended
    (B : BraidGroupDiagram.{u}) (η : B ⟶ B) (n : ℕ) :
    stageInjection B n ≫ descendedEndomorphism B η =
      η.app n ≫ stageInjection B n := by
  exact colimit.ι_map η n

/-- The descended first braid endomorphism read back on every finite stage. -/
theorem stageInjection_braid1
    (B : BraidGroupDiagram.{u}) (D : ArtinNaturalData B) (n : ℕ) :
    stageInjection B n ≫ descendedEndomorphism B D.braid1 =
      D.braid1.app n ≫ stageInjection B n :=
  stageInjection_descended B D.braid1 n

/-- The descended second braid endomorphism read back on every finite stage. -/
theorem stageInjection_braid2
    (B : BraidGroupDiagram.{u}) (D : ArtinNaturalData B) (n : ℕ) :
    stageInjection B n ≫ descendedEndomorphism B D.braid2 =
      D.braid2.app n ≫ stageInjection B n :=
  stageInjection_descended B D.braid2 n

/-- Artin's three-strand relation descends from every stage to the group
colimit. -/
theorem colimit_artin_relation
    (B : BraidGroupDiagram.{u}) (D : ArtinNaturalData B) :
    descendedEndomorphism B D.braid1 ≫
        descendedEndomorphism B D.braid2 ≫
        descendedEndomorphism B D.braid1 =
      descendedEndomorphism B D.braid2 ≫
        descendedEndomorphism B D.braid1 ≫
        descendedEndomorphism B D.braid2 := by
  apply colimit.hom_ext
  intro n
  calc
    stageInjection B n ≫
        descendedEndomorphism B D.braid1 ≫
        descendedEndomorphism B D.braid2 ≫
        descendedEndomorphism B D.braid1 =
      D.braid1.app n ≫ D.braid2.app n ≫ D.braid1.app n ≫
        stageInjection B n := by
          simpa only [Category.assoc] using
            congrArg (fun k =>
              k ≫ descendedEndomorphism B D.braid2 ≫
                descendedEndomorphism B D.braid1)
              (stageInjection_braid1 B D n)
    _ =
      D.braid2.app n ≫ D.braid1.app n ≫ D.braid2.app n ≫
        stageInjection B n := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ stageInjection B n) (D.artin n)
    _ =
      stageInjection B n ≫
        descendedEndomorphism B D.braid2 ≫
        descendedEndomorphism B D.braid1 ≫
        descendedEndomorphism B D.braid2 := by
          simpa only [Category.assoc] using
            congrArg (fun k =>
              k ≫ descendedEndomorphism B D.braid2 ≫
                descendedEndomorphism B D.braid1)
              (stageInjection_braid2 B D n).symm

/-- The categorical colimit preserves any stagewise relation between two
natural braid endomorphisms. -/
theorem colimit_relation_of_stagewise
    (B : BraidGroupDiagram.{u}) (η ξ : B ⟶ B)
    (h : ∀ n : ℕ, η.app n ≫ ξ.app n = ξ.app n ≫ η.app n) :
    descendedEndomorphism B η ≫ descendedEndomorphism B ξ =
      descendedEndomorphism B ξ ≫ descendedEndomorphism B η := by
  apply colimit.hom_ext
  intro n
  calc
    stageInjection B n ≫ descendedEndomorphism B η ≫
        descendedEndomorphism B ξ =
      η.app n ≫ ξ.app n ≫ stageInjection B n := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ descendedEndomorphism B ξ)
            (stageInjection_descended B η n)
    _ = ξ.app n ≫ η.app n ≫ stageInjection B n := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ stageInjection B n) (h n)
    _ = stageInjection B n ≫ descendedEndomorphism B ξ ≫
        descendedEndomorphism B η := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ descendedEndomorphism B η)
          (stageInjection_descended B ξ n).symm

/-- A compatible family of stage representations into a fixed group is a
cocone over the braid-group diagram. -/
abbrev RepresentationCocone
    (B : BraidGroupDiagram.{u}) (G : Grp.{u}) :=
  B ⟶ Functor.const ℕ G

/-- The corresponding categorical cocone. -/
abbrev representationCocone
    (B : BraidGroupDiagram.{u}) (G : Grp.{u})
    (ρ : RepresentationCocone B G) : Cocone B :=
  Cocone.mk G ρ

/-- The unique group homomorphism from the braid-group colimit induced by a
compatible family of stage representations. -/
abbrev descendedRepresentation
    (B : BraidGroupDiagram.{u}) (G : Grp.{u})
    (ρ : RepresentationCocone B G) :
    BraidGroupColimit B ⟶ G :=
  colimit.desc B (representationCocone B G ρ)

/-- The representation induced on each finite stage by the universal
colimit representation. -/
theorem stageInjection_descendedRepresentation
    (B : BraidGroupDiagram.{u}) (G : Grp.{u})
    (ρ : RepresentationCocone B G) (n : ℕ) :
    stageInjection B n ≫ descendedRepresentation B G ρ =
      ρ.app n := by
  exact colimit.ι_desc (representationCocone B G ρ) n

/-- The universal property makes the descended representation unique. -/
theorem descendedRepresentation_unique
    (B : BraidGroupDiagram.{u}) (G : Grp.{u})
    (ρ : RepresentationCocone B G)
    (f : BraidGroupColimit B ⟶ G)
    (h : ∀ n : ℕ, stageInjection B n ≫ f = ρ.app n) :
    f = descendedRepresentation B G ρ := by
  apply colimit.hom_ext
  intro n
  rw [h n, stageInjection_descendedRepresentation]

/-- The complete group-level braid-colimit packet. -/
theorem braid_group_colimit_artin_packet
    (B : BraidGroupDiagram.{u}) (D : ArtinNaturalData B) :
    (∀ n : ℕ,
      stageInjection B n ≫ descendedEndomorphism B D.braid1 =
        D.braid1.app n ≫ stageInjection B n) ∧
    (∀ n : ℕ,
      stageInjection B n ≫ descendedEndomorphism B D.braid2 =
        D.braid2.app n ≫ stageInjection B n) ∧
    descendedEndomorphism B D.braid1 ≫
        descendedEndomorphism B D.braid2 ≫
        descendedEndomorphism B D.braid1 =
      descendedEndomorphism B D.braid2 ≫
        descendedEndomorphism B D.braid1 ≫
        descendedEndomorphism B D.braid2 := by
  exact ⟨stageInjection_braid1 B D, stageInjection_braid2 B D,
    colimit_artin_relation B D⟩

end InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
