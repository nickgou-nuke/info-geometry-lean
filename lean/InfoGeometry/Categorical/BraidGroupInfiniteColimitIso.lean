import Mathlib
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

This closes the structural group-colimit theorem used by the Hadjiivanov braid
capstone: the repository-presented `B_∞` is not merely a compatible cocone
point, but is canonically isomorphic to Mathlib's categorical colimit of the
finite braid-group stabilization tower.
-/

noncomputable section

namespace InfoGeometry.Categorical.BraidGroupInfiniteColimitIso

open Braid
open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge

/-- The `i`th infinite Artin generator represented at its first finite stage
`B_{i+2}` and then inserted into the categorical colimit. -/
def colimitGenerator (i : ℕ) : braidGroupColimit :=
  colimit.ι braidGroupDiagram (i + 1)
    (σ' (i + 1) (⟨i, by omega⟩ : Fin (i + 1)))

/-- The colimit image of a fixed Artin generator is unchanged by any number of
successor stabilizations. -/
theorem colimitGenerator_stage_add (i k : ℕ) :
    colimitGenerator i =
      colimit.ι braidGroupDiagram (i + 1 + k)
        (σ' (i + 1 + k)
          (⟨i, by omega⟩ : Fin (i + 1 + k))) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [ih]
      let n := i + 1 + k
      have hw := colimit.w braidGroupDiagram (homOfLE (Nat.le_succ n))
      have happ := congrArg
        (fun f : braidGroupDiagram.obj n ⟶ braidGroupColimit =>
          f (σ' n (⟨i, by omega⟩ : Fin n))) hw
      have hstep :
          braidGroupDiagram.map (homOfLE (Nat.le_succ n)) =
            GrpCat.ofHom (finiteSuccGroupHom n) := by
        simpa [braidGroupDiagram] using
          (Functor.ofSequence_map_homOfLE_succ
            (f := fun n => GrpCat.ofHom (finiteSuccGroupHom n)) n)
      rw [hstep] at happ
      simpa [n, finiteSuccGroupHom_sigma] using happ.symm

/-- Convenient later-stage readback of the same colimit generator. -/
theorem colimitGenerator_stage
    (i n : ℕ) (h : i < n) :
    colimitGenerator i =
      colimit.ι braidGroupDiagram n
        (σ' n (⟨i, h⟩ : Fin n)) := by
  have hi : i + 1 ≤ n := by omega
  let k := n - (i + 1)
  have hk : i + 1 + k = n := by
    dsimp [k]
    omega
  simpa [hk] using colimitGenerator_stage_add i k

/-- Adjacent colimit generators satisfy the Artin relation. -/
theorem colimitGenerator_artin (i : ℕ) :
    colimitGenerator i * colimitGenerator (i + 1) * colimitGenerator i =
      colimitGenerator (i + 1) * colimitGenerator i *
        colimitGenerator (i + 1) := by
  let a : Fin (i + 1) := ⟨i, by omega⟩
  have hfinite := braid_group.braid (n := i) a
  have hmap := congrArg
    (fun g : braid_group (i + 3) =>
      colimit.ι braidGroupDiagram (i + 2) g) hfinite
  have hi := colimitGenerator_stage i (i + 2) (by omega)
  have hi1 := colimitGenerator_stage (i + 1) (i + 2) (by omega)
  simpa [hi, hi1, map_mul] using hmap

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
    dsimp [a, b]
    omega
  have hfinite := braid_group.comm (n := j) (i := a) (j := b) hab
  have hmap := congrArg
    (fun g : braid_group (j + 2) =>
      colimit.ι braidGroupDiagram (j + 1) g) hfinite
  have hi := colimitGenerator_stage i (j + 1) (by omega)
  have hj := colimitGenerator_stage j (j + 1) (by omega)
  simpa [a, b, hi, hj, Nat.sub_add_cancel hj2, map_mul] using hmap

/-- Every defining relation of the presented infinite braid group holds for the
canonical generator images in the finite-stage group colimit. -/
theorem colimitGenerator_relations :
    ∀ r ∈ braid_rels_inf,
      FreeGroup.lift colimitGenerator r = (1 : braidGroupColimit) := by
  intro r hr
  rcases hr with hArtin | hFar
  · rcases hArtin with ⟨i, rfl⟩
    have h := colimitGenerator_artin i
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [h]
    group
  · rcases hFar with ⟨i, j, hij, rfl⟩
    have h := colimitGenerator_far i j hij
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [h]
    group

/-- Canonical inverse comparison from the presented `B_∞` to Mathlib's finite
braid-group colimit. -/
def infiniteToGroupColimit : braid_group_inf →* braidGroupColimit :=
  braid_group_inf.toGroup colimitGenerator colimitGenerator_relations

@[simp]
theorem infiniteToGroupColimit_sigma (i : ℕ) :
    infiniteToGroupColimit (σi i) = colimitGenerator i := by
  exact braid_group_inf.toGroup_sigma
    colimitGenerator colimitGenerator_relations i

/-- The inverse comparison restricts on every finite stage to the canonical
colimit injection. -/
theorem infiniteToGroupColimit_comp_finiteToInfinite (n : ℕ) :
    infiniteToGroupColimit.comp (finiteToInfiniteGroupHom n) =
      (colimit.ι braidGroupDiagram n).hom := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply, finiteToInfiniteGroupHom_sigma,
    infiniteToGroupColimit_sigma]
  exact colimitGenerator_stage i.1 n i.2

/-- The canonical comparison followed by the generator-defined inverse is the
identity on the categorical finite-stage colimit. -/
theorem groupFromColimit_hom_inv :
    groupFromColimit ≫ GrpCat.ofHom infiniteToGroupColimit =
      𝟙 braidGroupColimit := by
  apply colimit.hom_ext
  intro n
  apply GrpCat.hom_ext
  change infiniteToGroupColimit.comp
      ((colimit.ι braidGroupDiagram n ≫ groupFromColimit).hom) =
    (colimit.ι braidGroupDiagram n).hom
  rw [groupFromColimit_ι]
  exact infiniteToGroupColimit_comp_finiteToInfinite n

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
  simp [colimitGenerator, groupFromColimit_ι_apply,
    finiteToInfiniteGroupHom_sigma]

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
  exact (colimit.isColimit braidGroupDiagram).ofPointIso
    braidGroupColimitIsoInfinite

end InfoGeometry.Categorical.BraidGroupInfiniteColimitIso