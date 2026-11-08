import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge

/-!
# The presented infinite braid group is the colimit of the finite braid tower

The repository already owns both sides of this statement:

* `Braid.braid_group_inf`, presented on countably many Artin generators;
* `braidGroupColimit`, Mathlib's `GrpCat` colimit of the finite stabilization
  tower `B₁ → B₂ → ⋯`.

This file constructs the inverse of the existing comparison
`groupFromColimit : braidGroupColimit ⟶ GrpCat.of braid_group_inf` directly on
Artin generators.  No new braid presentation is introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.BraidGroupInfiniteColimitIso

open Braid
open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge

/-- A finite Artin generator viewed in the underlying carrier of its diagram
stage. -/
def stageArtinGenerator (n : ℕ) (i : Fin n) : braid_group (n + 1) :=
  σ' n i

/-- Identify the concrete finite braid group with the carrier stored in its
`GrpCat` stage. -/
def stageCarrierEquiv (n : ℕ) : braid_group (n + 1) ≃* braidGroupDiagram.obj n where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := by intros; rfl

@[simp]
theorem stageCarrierEquiv_apply (n : ℕ) (g : braid_group (n + 1)) :
    stageCarrierEquiv n g = g := rfl

@[simp]
theorem stageCarrierEquiv_symm_apply (n : ℕ) (g : braidGroupDiagram.obj n) :
    (stageCarrierEquiv n).symm g = g := rfl

@[simp]
theorem stageCarrierEquiv_symm_eq_apply (n : ℕ) (g : braid_group (n + 1)) :
    (stageCarrierEquiv n).symm g = stageCarrierEquiv n g := rfl

@[simp]
theorem stageCarrierEquiv_symm_stageArtinGenerator (n : ℕ) (i : Fin n) :
    (stageCarrierEquiv n).symm (stageArtinGenerator n i) =
      stageArtinGenerator n i := rfl

@[simp]
theorem stageCarrierEquiv_symm_toMonoidHom_apply
    (n : ℕ) (g : braidGroupDiagram.obj n) :
    (stageCarrierEquiv n).symm.toMonoidHom g = g := rfl

@[simp]
theorem stageCarrierEquiv_symm_toMonoidHom_sigma
    (n : ℕ) (i : Fin n) :
    (stageCarrierEquiv n).symm.toMonoidHom (σ' n i) = σ' n i := rfl

/-- The same Artin generator, typed in the bundled diagram object. -/
def stageArtinGeneratorInDiagram (n : ℕ) (i : Fin n) : braidGroupDiagram.obj n :=
  stageCarrierEquiv n (stageArtinGenerator n i)

/-- The colimit inclusion, expressed on the concrete finite braid-group
carrier rather than through the category's bundled carrier coercion. -/
def colimitStageMap (n : ℕ) : braid_group (n + 1) →*
    (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).pt := by
  exact (((GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n).hom).comp
    (stageCarrierEquiv n).toMonoidHom

/-- Evaluation of a concrete stage generator through the bundled colimit
inclusion agrees with applying the inclusion to its bundled-stage readback. -/
theorem colimitStageMap_stageGenerator (n : ℕ) (i : Fin n) :
    colimitStageMap n (stageArtinGenerator n i) =
      (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n
        (stageArtinGeneratorInDiagram n i) := by
  rfl

@[simp]
theorem colimitStageMap_apply (n : ℕ) (g : braid_group (n + 1)) :
    colimitStageMap n g =
      (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n g := rfl

/-- The `i`th infinite Artin generator represented at its first finite stage
`B_{i+2}` and then inserted into the categorical colimit. -/
def colimitGenerator (i : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).pt :=
  colimitStageMap (i + 1) (stageArtinGenerator (i + 1) ⟨i, by omega⟩)

/-- The colimit image of a fixed Artin generator is unchanged by any number of
successor stabilizations. -/
theorem colimitGenerator_stage_add (i k : ℕ) :
    colimitGenerator i =
      colimitStageMap (i + 1 + k)
        (stageArtinGenerator (i + 1 + k) ⟨i, by omega⟩) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [ih]
      let n := i + 1 + k
      have hw := (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).w
        (homOfLE (Nat.le_succ n))
      have hstep : braidGroupDiagram.map (homOfLE (Nat.le_succ n)) =
          GrpCat.ofHom (finiteSuccGroupHom n) := by
        simp only [braidGroupDiagram, Functor.ofSequence_map_homOfLE_succ]
        rfl
      have happ := congrArg
        (fun f : braidGroupDiagram.obj n ⟶ braidGroupColimit =>
          f (stageArtinGeneratorInDiagram n ⟨i, by omega⟩)) hw
      change (braidGroupDiagram.map (homOfLE (Nat.le_succ n)) ≫
          (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n.succ)
          (stageArtinGeneratorInDiagram n ⟨i, by omega⟩) =
        (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n
          (stageArtinGeneratorInDiagram n ⟨i, by omega⟩) at happ
      rw [GrpCat.comp_apply] at happ
      have hmap' := congrArg
        (fun f : braidGroupDiagram.obj n ⟶ braidGroupDiagram.obj n.succ =>
          f (stageArtinGeneratorInDiagram n ⟨i, by omega⟩)) hstep
      have hhom : (GrpCat.ofHom (finiteSuccGroupHom n))
            (stageArtinGeneratorInDiagram n ⟨i, by omega⟩) =
          stageArtinGeneratorInDiagram n.succ ⟨i, by omega⟩ := by
        simp only [stageArtinGeneratorInDiagram, stageArtinGenerator,
          stageCarrierEquiv_apply]
        exact finiteSuccGroupHom_sigma n ⟨i, by omega⟩
      have hmap : braidGroupDiagram.map (homOfLE (Nat.le_succ n))
            (stageArtinGeneratorInDiagram n ⟨i, by omega⟩) =
          stageArtinGeneratorInDiagram n.succ ⟨i, by omega⟩ := by
        exact hmap'.trans hhom
      rw [hmap] at happ
      calc
        colimitStageMap (i + 1 + k) (stageArtinGenerator (i + 1 + k) ⟨i, by omega⟩) =
            (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n
              (stageArtinGeneratorInDiagram n ⟨i, by omega⟩) := by
          simpa [n] using colimitStageMap_stageGenerator (i + 1 + k) ⟨i, by omega⟩
        _ = (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n.succ
              (stageArtinGeneratorInDiagram n.succ ⟨i, by omega⟩) := happ.symm
        _ = colimitStageMap (i + 1 + (k + 1))
              (stageArtinGenerator (i + 1 + (k + 1)) ⟨i, by omega⟩) := by
          symm
          have hidx : i + 1 + (k + 1) = n.succ := by
            dsimp [n]
            omega
          change colimitStageMap (i + 1 + (k + 1))
              (stageArtinGenerator (i + 1 + (k + 1)) ⟨i, by omega⟩) =
            (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app
              (i + 1 + (k + 1))
              (stageArtinGeneratorInDiagram (i + 1 + (k + 1)) ⟨i, by omega⟩)
          exact colimitStageMap_stageGenerator (i + 1 + (k + 1)) ⟨i, by omega⟩

/-- Convenient later-stage readback of the same colimit generator. -/
theorem colimitGenerator_stage
    (i n : ℕ) (h : i < n) :
    colimitGenerator i =
      colimitStageMap n (stageArtinGenerator n ⟨i, h⟩) := by
  have hi : i + 1 ≤ n := by omega
  revert h
  let k := n - (i + 1)
  have hk : i + 1 + k = n := by
    dsimp [k]
    omega
  have hs := colimitGenerator_stage_add i k
  dsimp [k] at hs
  have harith : i + 1 + (n - (i + 1)) = n := by omega
  rw [← harith]
  intro h
  simpa using hs

/-- Adjacent colimit generators satisfy the Artin relation. -/
theorem colimitGenerator_artin (i : ℕ) :
    colimitGenerator i * colimitGenerator (i + 1) * colimitGenerator i =
      colimitGenerator (i + 1) * colimitGenerator i *
        colimitGenerator (i + 1) := by
  let a : Fin (i + 1) := ⟨i, by omega⟩
  have hfinite := braid_group.braid (n := i) a
  let f : braid_group (i + 3) →* (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).pt := by
    simpa [Nat.add_assoc] using colimitStageMap (i + 2)
  have hmap := congrArg f hfinite
  have hi := colimitGenerator_stage i (i + 2) (by omega)
  have hi1 := colimitGenerator_stage (i + 1) (i + 2) (by omega)
  simp only [map_mul] at hmap
  simp only [σ, σ'] at hmap
  have hmap' : f (stageArtinGenerator (i + 2) ⟨i, by omega⟩) *
      f (stageArtinGenerator (i + 2) ⟨i + 1, by omega⟩) *
      f (stageArtinGenerator (i + 2) ⟨i, by omega⟩) =
    f (stageArtinGenerator (i + 2) ⟨i + 1, by omega⟩) *
      f (stageArtinGenerator (i + 2) ⟨i, by omega⟩) *
      f (stageArtinGenerator (i + 2) ⟨i + 1, by omega⟩) := by
    simpa [a, stageArtinGenerator, σ, σ'] using hmap
  rw [← hi, ← hi1] at hmap'
  exact hmap'

/-- Separated colimit generators commute. -/
theorem colimitGenerator_far
    (i j : ℕ) (hij : i + 2 ≤ j) :
    colimitGenerator i * colimitGenerator j =
      colimitGenerator j * colimitGenerator i := by
  have hj2 : 2 ≤ j := by omega
  let a : Fin j := ⟨i, by omega⟩
  let b : Fin j := ⟨j - 2, by omega⟩
  have hab : a ≤ b := by
    apply Fin.mk_le_mk.mpr
    omega
  have hfinite := braid_group.comm (n := j) (i := a) (j := b) hab
  let f : braid_group (j + 2 + 1) →*
      (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).pt :=
    colimitStageMap (j + 2)
  have hmap := congrArg f hfinite
  have hi := colimitGenerator_stage i (j + 2) (by omega)
  have hj := colimitGenerator_stage j (j + 2) (by omega)
  simp only [map_mul] at hmap
  simp only [σ, σ'] at hmap
  simp [b, Nat.sub_add_cancel hj2] at hmap
  have hmap' : f (stageArtinGenerator (j + 2) ⟨i, by omega⟩) *
      f (stageArtinGenerator (j + 2) ⟨j, by omega⟩) =
      f (stageArtinGenerator (j + 2) ⟨j, by omega⟩) *
        f (stageArtinGenerator (j + 2) ⟨i, by omega⟩) := by
    simpa [a, b, stageArtinGenerator, σ, σ'] using hmap
  rw [← hi, ← hj] at hmap'
  exact hmap'

/-- Every defining relation of the presented infinite braid group holds for the
canonical generator images in the finite-stage group colimit. -/
theorem colimitGenerator_relations :
    ∀ r ∈ braid_rels_inf,
      FreeGroup.lift colimitGenerator r = (1 : braidGroupColimit) := by
  intro r hr
  rcases hr with hArtin | hFar
  · rcases hArtin with ⟨i, rfl⟩
    change FreeGroup.lift colimitGenerator (Braid.braid_rel i (i + 1)) =
      (1 : (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).pt)
    exact InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.freeGroup_lift_braid_relator
      colimitGenerator i (i + 1) (colimitGenerator_artin i)
  · rcases hFar with ⟨i, j, hij, rfl⟩
    change FreeGroup.lift colimitGenerator (Braid.comm_rel i j) =
      (1 : (GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).pt)
    exact InfoGeometry.Categorical.HadjiivanovBraidGroupColimit.freeGroup_lift_comm_relator
      colimitGenerator i j (colimitGenerator_far i j hij)

/-- Canonical inverse comparison from the presented `B_∞` to Mathlib's finite
braid-group colimit. -/
def infiniteToGroupColimit : braid_group_inf →* braidGroupColimit :=
  PresentedGroup.toGroup (f := colimitGenerator)
    (rels := braid_rels_inf) colimitGenerator_relations

@[simp]
theorem infiniteToGroupColimit_sigma (i : ℕ) :
    infiniteToGroupColimit (σi i) = colimitGenerator i := by
  exact PresentedGroup.toGroup.of colimitGenerator_relations

/-- The inverse comparison restricts on every finite stage to the canonical
colimit injection. -/
theorem infiniteToGroupColimit_comp_finiteToInfinite (n : ℕ) :
    infiniteToGroupColimit.comp (finiteToInfiniteGroupHom n) =
      colimitStageMap n := by
  apply PresentedGroup.ext
  intro i
  change infiniteToGroupColimit
      (finiteToInfiniteGroupHom n (σ' n i)) =
    colimitStageMap n (σ' n i)
  rw [finiteToInfiniteGroupHom_sigma, infiniteToGroupColimit_sigma]
  exact colimitGenerator_stage i.1 n i.2

/-- The canonical comparison followed by the generator-defined inverse is the
identity on the categorical finite-stage colimit. -/
theorem groupFromColimit_hom_inv :
    groupFromColimit ≫ GrpCat.ofHom infiniteToGroupColimit =
      𝟙 braidGroupColimit := by
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit braidGroupDiagram).hom_ext
  intro n
  apply GrpCat.hom_ext
  change infiniteToGroupColimit.comp
      (((GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n ≫
        groupFromColimit).hom) =
    ((GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n).hom
  rw [groupFromColimit_ι]
  apply MonoidHom.ext
  intro x
  have h := congrArg
    (fun f : braid_group (n + 1) →* braidGroupColimit =>
      f ((stageCarrierEquiv n).symm x))
    (infiniteToGroupColimit_comp_finiteToInfinite n)
  change infiniteToGroupColimit
      (finiteToInfiniteGroupHom n ((stageCarrierEquiv n).symm x)) =
    (colimitStageMap n) ((stageCarrierEquiv n).symm x) at h
  rw [stageCarrierEquiv_symm_apply] at h
  change infiniteToGroupColimit
      ((GrpCat.ofHom (finiteToInfiniteGroupHom n)).hom x) =
    ((GrpCat.FilteredColimits.colimitCocone braidGroupDiagram).ι.app n).hom x
  rw [GrpCat.hom_ofHom]
  exact h

/-- The generator-defined inverse followed by the canonical comparison is the
identity on the presented infinite braid group. -/
theorem groupFromColimit_inv_hom :
    GrpCat.ofHom infiniteToGroupColimit ≫ groupFromColimit =
      𝟙 (GrpCat.of braid_group_inf) := by
  apply GrpCat.hom_ext
  apply PresentedGroup.ext
  intro i
  change groupFromColimit (infiniteToGroupColimit (σi i)) = σi i
  rw [infiniteToGroupColimit_sigma]
  have h := groupFromColimit_ι_apply (i + 1)
    (σ' (i + 1) (⟨i, by omega⟩ : Fin (i + 1)))
  simpa [colimitGenerator, stageArtinGenerator,
    stageCarrierEquiv_symm_apply, colimitStageMap_apply,
    finiteToInfiniteGroupHom_sigma] using h

/-- Canonical group-category isomorphism
`colim_n B_n ≅ B_∞`. -/
def braidGroupColimitIsoInfinite :
    braidGroupColimit ≅ GrpCat.of braid_group_inf where
  hom := groupFromColimit
  inv := GrpCat.ofHom infiniteToGroupColimit
  hom_inv_id := groupFromColimit_hom_inv
  inv_hom_id := groupFromColimit_inv_hom

/-- The existing comparison morphism is an isomorphism. -/
noncomputable instance groupFromColimit_isIso : IsIso groupFromColimit :=
  braidGroupColimitIsoInfinite.isIso_hom

/-- The repository-presented infinite braid group is itself a genuine Mathlib
colimit of the finite braid-group stabilization tower. -/
def braidGroupBoundaryCoconeIsColimit :
    IsColimit braidGroupBoundaryCocone := by
  letI : IsIso groupFromColimit := groupFromColimit_isIso
  letI : IsIso
      ((GrpCat.FilteredColimits.colimitCoconeIsColimit braidGroupDiagram).desc
        braidGroupBoundaryCocone) := groupFromColimit_isIso
  exact (GrpCat.FilteredColimits.colimitCoconeIsColimit braidGroupDiagram).ofPointIso

end InfoGeometry.Categorical.BraidGroupInfiniteColimitIso
