import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.NatTrans
import proofs.BraidProject.BraidGroup
import proofs.BraidInductiveColimitCategory

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

/-- The finite stage with n adjacent braid generators. -/
abbrev finiteBraidStage (n : ℕ) : Grp :=
  Braid.braid_group (n + 1)

/-- The existing finite-stage generator included into the next stage by adding
a straight strand on the right. -/
def straightStrandGenerator (n : ℕ) (i : Fin n) :
    finiteBraidStage (n + 1) :=
  Braid.σ' (n + 1) i.castSucc

/-- The relation-respecting condition required to turn the straight-strand
generator assignment into a homomorphism of presented groups. -/
abbrev straightStrandRelators (n : ℕ) : Prop :=
  ∀ r : FreeGroup (Fin n), r ∈ Braid.braid_rels n →
    FreeGroup.lift (straightStrandGenerator n) r = 1

/-- The finite straight-strand homomorphism, constructed from the existing
presentations once their relators are shown to be preserved. -/
noncomputable def straightStrandBond
    (n : ℕ) (h : straightStrandRelators n) :
    finiteBraidStage n →* finiteBraidStage (n + 1) :=
  PresentedGroup.toGroup (f := straightStrandGenerator n)
    (rels := Braid.braid_rels n) h

/-- The straight-strand homomorphism agrees with the generator assignment. -/
@[simp] theorem straightStrandBond_on_generator
    (n : ℕ) (h : straightStrandRelators n) (i : Fin n) :
    straightStrandBond n h (Braid.σ' n i) =
      straightStrandGenerator n i := by
  exact PresentedGroup.toGroup.of h

/-- A group-level Artin equality is exactly the free-group relator
condition used by PresentedGroup.toGroup. -/
theorem freeGroup_lift_braid_relator
    {α G : Type*} [Group G] (f : α → G) (a b : α)
    (h : f a * f b * f a = f b * f a * f b) :
    FreeGroup.lift f (Braid.braid_rel a b) = 1 := by
  simp only [Braid.braid_rel, map_mul, map_inv,
    FreeGroup.lift_apply_of]
  simpa [mul_assoc] using (mul_inv_eq_one.mpr h)

/-- A group-level commutation equality is exactly the free-group relator
condition for the repository's comm_rel presentation word. -/
theorem freeGroup_lift_comm_relator
    {α G : Type*} [Group G] (f : α → G) (a b : α)
    (h : f a * f b = f b * f a) :
    FreeGroup.lift f (Braid.comm_rel a b) = 1 := by
  simp only [Braid.comm_rel, map_mul, map_inv,
    FreeGroup.lift_apply_of]
  simpa [mul_assoc] using (mul_inv_eq_one.mpr h)

/-- The relation-preservation obligation can be checked on the two
presentation families: adjacent braid words and separated commutators. -/
abbrev straightStrandRelatorsChecked (n : ℕ) : Prop :=
  ∀ r : FreeGroup (Fin n), r ∈ Braid.braid_rels n →
    FreeGroup.lift (straightStrandGenerator n) r = 1

/-- The checked relator predicate is definitionally the predicate used to
construct the finite straight-strand homomorphism. -/
theorem straightStrandRelatorsChecked_eq
    (n : ℕ) :
    straightStrandRelatorsChecked n = straightStrandRelators n := by
  rfl

/-- The adjacent finite relator is preserved by adding a straight strand. -/
theorem canonicalStraightStrand_adjacent
    (n : ℕ) (i : Fin (n + 1)) :
    FreeGroup.lift (straightStrandGenerator (n + 2))
        (Braid.braid_rel i.castSucc i.succ) = 1 := by
  have hindex : i.castSucc.succ = i.succ.castSucc := by
    apply Fin.ext
    rfl
  have hrel := Braid.braid_group.braid (n := n + 1) i.castSucc
  have hrel' :
      straightStrandGenerator (n + 2) i.castSucc *
          straightStrandGenerator (n + 2) i.succ *
          straightStrandGenerator (n + 2) i.castSucc =
        straightStrandGenerator (n + 2) i.succ *
          straightStrandGenerator (n + 2) i.castSucc *
          straightStrandGenerator (n + 2) i.succ := by
    simpa [straightStrandGenerator, Braid.σ, Braid.σ', hindex] using hrel
  exact freeGroup_lift_braid_relator
    (straightStrandGenerator (n + 2)) i.castSucc i.succ hrel'

/-- The far finite relator is preserved by adding a straight strand. -/
theorem canonicalStraightStrand_far
    (n : ℕ) (i j : Fin n) (hij : i ≤ j) :
    FreeGroup.lift (straightStrandGenerator (n + 2))
        (Braid.comm_rel i.castSucc.castSucc j.succ.succ) = 1 := by
  have hright :
      j.castSucc.succ.succ = j.succ.succ.castSucc := by
    apply Fin.ext
    rfl
  have hrel := Braid.braid_group.comm
    (n := n + 1) (i := i.castSucc) (j := j.castSucc)
    (by exact hij)
  have hrel' :
      straightStrandGenerator (n + 2) i.castSucc.castSucc *
          straightStrandGenerator (n + 2) j.succ.succ =
        straightStrandGenerator (n + 2) j.succ.succ *
          straightStrandGenerator (n + 2) i.castSucc.castSucc := by
    simpa [straightStrandGenerator, Braid.σ, Braid.σ', hright] using hrel
  exact freeGroup_lift_comm_relator
    (straightStrandGenerator (n + 2))
    i.castSucc.castSucc j.succ.succ hrel'

/-- The complete canonical relator-preservation theorem for the finite
presented braid tower. -/
theorem canonicalStraightStrandRelators (n : ℕ) :
    straightStrandRelators n := by
  cases n with
  | zero =>
      intro r hr
      exact (Set.not_mem_empty r hr).elim
  | succ n =>
      cases n with
      | zero =>
          intro r hr
          exact (Set.not_mem_empty r hr).elim
      | succ n =>
          intro r hr
          change r ∈
            ({ r | ∃ i : Fin (n + 1),
                r = Braid.braid_rel i.castSucc i.succ } ∪
              { r | ∃ i j : Fin n, i ≤ j ∧
                r = Braid.comm_rel i.castSucc.castSucc j.succ.succ }) at hr
          rcases hr with hr | hr
          · rcases hr with ⟨i, rfl⟩
            exact canonicalStraightStrand_adjacent n i
          · rcases hr with ⟨i, j, hij, rfl⟩
            exact canonicalStraightStrand_far n i j hij

/-- The finite presented braid tower input: all existing Artin relators are
preserved by the straight-strand generator assignment. -/
structure FinitePresentedBraidTowerInput where
  relators : ∀ n : ℕ, straightStrandRelators n

/-- The finite presented braid tower with its canonical straight-strand
relator witnesses. -/
def canonicalFinitePresentedBraidTowerInput :
    FinitePresentedBraidTowerInput where
  relators := canonicalStraightStrandRelators

/-- The canonical tower datum on the repository's finite presented braid
groups. -/
def canonicalBraidGroupTower : BraidGroupTower.{0} where
  stage := finiteBraidStage
  bond := fun n => straightStrandBond n
    (canonicalFinitePresentedBraidTowerInput.relators n)

/-- The concrete finite presented braid-group diagram generated by a proved
straight-strand relator family. -/
def finitePresentedBraidDiagram
    (T : FinitePresentedBraidTowerInput) : BraidGroupDiagram :=
  Functor.ofSequence (fun n => straightStrandBond n (T.relators n))


/-- The tower diagram is the concrete finite presented braid diagram. -/
theorem canonicalBraidGroupTower_diagram :
    canonicalBraidGroupTower.diagram =
      finitePresentedBraidDiagram canonicalFinitePresentedBraidTowerInput := by
  rfl

/-- The categorical colimit of the canonical finite presented braid tower. -/
abbrev canonicalBraidGroupColimit : Grp :=
  BraidGroupColimit canonicalBraidGroupTower.diagram

/-- Its categorical colimit is the infinite braid group associated with the
finite presented tower. -/
abbrev finitePresentedBraidColimit
    (T : FinitePresentedBraidTowerInput) : Grp :=
  colimit (finitePresentedBraidDiagram T)

/-- The finite generator/word boundary is compatible with the concrete
presented-stage generator assignment. -/
theorem finitePresentedBraidGenerator_boundary
    (T : FinitePresentedBraidTowerInput) (n : ℕ) (i : Fin n) :
    straightStrandBond n (T.relators n) (Braid.σ' n i) =
      Braid.σ' (n + 1) i.castSucc :=
  straightStrandBond_on_generator n (T.relators n) i

/-- The finite presented tower specializes the previously proved generator
successor map Fin.castSucc; the remaining work is solely relator preservation. -/
theorem finitePresentedBraidTower_synthesis
    (T : FinitePresentedBraidTowerInput) :
    (∀ n : ℕ, ∀ i : Fin n,
      straightStrandBond n (T.relators n) (Braid.σ' n i) =
        Braid.σ' (n + 1) i.castSucc) ∧
    (finitePresentedBraidColimit T =
      colimit (finitePresentedBraidDiagram T)) := by
  exact ⟨fun n i => finitePresentedBraidGenerator_boundary T n i, rfl⟩

/-- The same categorical colimit under the shorter braid-specific name used
by the Hadjiivanov representation layer. -/
abbrev BraidColimit (B : BraidGroupDiagram.{u}) : Grp.{u} :=
  BraidGroupColimit B

/-- Universal stage inclusion under the braid-specific API name. -/
abbrev stageInclusion (B : BraidGroupDiagram.{u}) (n : ℕ) :
    B.obj n ⟶ BraidColimit B :=
  stageInjection B n

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

/-- A compatible representation cocone descends to a single group
homomorphism out of the categorical braid colimit. -/
abbrev descendedRep
    (B : BraidGroupDiagram.{u}) (rep_family : Cocone B) :
    BraidColimit B ⟶ rep_family.pt :=
  colimit.desc B rep_family

/-- The descended representation restricts to the prescribed stage map. -/
theorem rep_stage_commutation
    (B : BraidGroupDiagram.{u}) (rep_family : Cocone B) (n : ℕ) :
    stageInclusion B n ≫ descendedRep B rep_family =
      rep_family.ι.app n := by
  exact colimit.ι_desc rep_family n

/-- Uniqueness of a descended representation from all stage inclusions. -/
theorem rep_uniqueness
    (B : BraidGroupDiagram.{u}) (rep_family : Cocone B)
    (f g : BraidColimit B ⟶ rep_family.pt)
    (h_eq : ∀ n : ℕ, stageInclusion B n ≫ f =
      stageInclusion B n ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro n
  exact h_eq n

/-- Pointwise commutation descends through a Grp stage inclusion. -/
theorem descended_commutation
    (B : BraidGroupDiagram.{u}) {n : ℕ} (x y : B.obj n)
    (h_comm : x * y = y * x) :
    (stageInclusion B n) x * (stageInclusion B n) y =
      (stageInclusion B n) y * (stageInclusion B n) x := by
  let ι_n : B.obj n →* BraidColimit B := stageInclusion B n
  change ι_n x * ι_n y = ι_n y * ι_n x
  simpa only [map_mul] using congrArg ι_n h_comm

/-- Pointwise Artin braid relation descent through a Grp stage inclusion. -/
theorem descended_artin_relation
    (B : BraidGroupDiagram.{u}) {n : ℕ} {x y : B.obj n}
    (h_artin : x * y * x = y * x * y) :
    (stageInclusion B n) x * (stageInclusion B n) y *
        (stageInclusion B n) x =
      (stageInclusion B n) y * (stageInclusion B n) x *
        (stageInclusion B n) y := by
  let ι_n : B.obj n →* BraidColimit B := stageInclusion B n
  change ι_n x * ι_n y * ι_n x = ι_n y * ι_n x * ι_n y
  simpa only [map_mul] using congrArg ι_n h_artin

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
