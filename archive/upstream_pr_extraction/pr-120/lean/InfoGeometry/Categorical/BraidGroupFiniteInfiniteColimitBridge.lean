import Mathlib
import proofs.BraidProject.BraidGroup
import proofs.BraidInductiveColimitCategory

/-!
# Finite braid groups and the infinite braid boundary

This file welds two repository-owned layers which were previously formalized
separately:

* `proofs.BraidProject.BraidGroup` owns the presented finite braid groups
  `B_n`, the infinite braid group `B_∞`, and the Artin/far-commutation laws;
* `proofs.BraidInductiveColimitCategory` owns the categorical colimit of the
  finite generator and finite-word towers.

No new braid presentation is introduced.  We construct the canonical group
homomorphisms induced by the existing generator inclusions, prove their
stabilization compatibility, and package them as a Mathlib `GrpCat` cocone.
-/

noncomputable section

namespace InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge

open Braid
open BraidInductiveColimitComplement
open CategoryTheory
open CategoryTheory.Limits

/-- Every defining relation of the finite stage is satisfied by the
corresponding generators in `B_∞`. -/
theorem finiteRelations_hold_in_infinite (n : ℕ) :
    ∀ r ∈ braid_rels n,
      FreeGroup.lift (fun i : Fin n => σi i.1) r = (1 : braid_group_inf) := by
  intro r hr
  cases n with
  | zero =>
      simpa [braid_rels] using hr
  | succ n =>
      cases n with
      | zero =>
          simpa [braid_rels] using hr
      | succ n =>
          rcases hr with hAdj | hFar
          · rcases hAdj with ⟨i, rfl⟩
            have hArtin := braid_group_inf.braid i.1
            simp [braid_rels, braid_rel, FreeGroup.lift_apply_of,
              Nat.succ_eq_add_one, mul_assoc]
            rw [hArtin]
            group
          · rcases hFar with ⟨i, j, hij, rfl⟩
            have hijv : i.1 ≤ j.1 := by exact hij
            have hsep : i.1 + 2 ≤ j.1 + 2 := Nat.add_le_add_right hijv 2
            have hComm := braid_group_inf.comm hsep
            simp [braid_rels, comm_rel, FreeGroup.lift_apply_of,
              Nat.succ_eq_add_one, mul_assoc]
            rw [hComm]
            group

/-- Canonical group homomorphism `B_{n+1} → B_∞`, sending the finite generator
`σ_i` to the infinite generator with the same index. -/
noncomputable def finiteToInfiniteGroupHom (n : ℕ) :
    braid_group (n + 1) →* braid_group_inf :=
  braid_group.toGroup (fun i : Fin n => σi i.1)
    (finiteRelations_hold_in_infinite n)

@[simp]
theorem finiteToInfiniteGroupHom_sigma
    (n : ℕ) (i : Fin n) :
    finiteToInfiniteGroupHom n (σ' n i) = σi i.1 := by
  exact braid_group.toGroup_sigma
    (fun i : Fin n => σi i.1) (finiteRelations_hold_in_infinite n) i

/-- Every defining relation at stage `n` is also satisfied after the successor
inclusion of generators into stage `n+1`. -/
theorem finiteRelations_hold_after_succ (n : ℕ) :
    ∀ r ∈ braid_rels n,
      FreeGroup.lift
        (fun i : Fin n => (σ' (n + 1) i.castSucc : braid_group (n + 2))) r = 1 := by
  intro r hr
  cases n with
  | zero =>
      simpa [braid_rels] using hr
  | succ n =>
      cases n with
      | zero =>
          simpa [braid_rels] using hr
      | succ n =>
          rcases hr with hAdj | hFar
          · rcases hAdj with ⟨i, rfl⟩
            have hArtin := braid_group.braid (n := n + 1) i.castSucc
            simp [braid_rels, braid_rel, FreeGroup.lift_apply_of,
              Nat.succ_eq_add_one, mul_assoc]
            rw [hArtin]
            group
          · rcases hFar with ⟨i, j, hij, rfl⟩
            have hComm := braid_group.comm
              (n := n + 1) (i := i.castSucc) (j := j.succ) hij
            simp [braid_rels, comm_rel, FreeGroup.lift_apply_of,
              Nat.succ_eq_add_one, mul_assoc]
            rw [hComm]
            group

/-- Standard stabilization `B_{n+1} → B_{n+2}` induced by `Fin.castSucc` on
Artin generators. -/
noncomputable def finiteSuccGroupHom (n : ℕ) :
    braid_group (n + 1) →* braid_group (n + 2) :=
  braid_group.toGroup
    (fun i : Fin n => (σ' (n + 1) i.castSucc : braid_group (n + 2)))
    (finiteRelations_hold_after_succ n)

@[simp]
theorem finiteSuccGroupHom_sigma
    (n : ℕ) (i : Fin n) :
    finiteSuccGroupHom n (σ' n i) = σ' (n + 1) i.castSucc := by
  exact braid_group.toGroup_sigma
    (fun i : Fin n => (σ' (n + 1) i.castSucc : braid_group (n + 2)))
    (finiteRelations_hold_after_succ n) i

/-- The finite-to-infinite group maps form a cocone over stabilization:
embedding after one finite stabilization is exactly the original embedding. -/
theorem finiteToInfiniteGroupHom_succ_compatible (n : ℕ) :
    (finiteToInfiniteGroupHom (n + 1)).comp (finiteSuccGroupHom n) =
      finiteToInfiniteGroupHom n := by
  apply braid_group.toGroup_unique
    (fun i : Fin n => σi i.1)
    (finiteRelations_hold_in_infinite n)
  intro i
  simp

/-- Pointwise compatibility form of the finite braid-group cocone. -/
theorem finiteToInfiniteGroupHom_succ_apply
    (n : ℕ) (g : braid_group (n + 1)) :
    finiteToInfiniteGroupHom (n + 1) (finiteSuccGroupHom n g) =
      finiteToInfiniteGroupHom n g := by
  exact MonoidHom.congr_fun (finiteToInfiniteGroupHom_succ_compatible n) g

/-- The group-level generator embedding agrees with the already-owned
finite-generator colimit boundary map. -/
theorem group_generator_matches_colimit_boundary
    (n : ℕ) (i : FiniteBraidGenerators n) :
    finiteToInfiniteGroupHom n (σ' n i) =
      σi (generatorFromColimit
        (colimit.ι braidGeneratorDiagram n i)) := by
  rw [generatorFromColimit_ι]
  exact finiteToInfiniteGroupHom_sigma n i

/-! ## Mathlib group-category cocone -/

/-- The finite braid-group tower as a sequence in Mathlib's category of groups. -/
def braidGroupDiagram : ℕ ⥤ GrpCat :=
  Functor.ofSequence
    (fun n => GrpCat.ofHom (finiteSuccGroupHom n))

/-- The existing infinite braid group as a cocone point for the finite tower. -/
def braidGroupBoundaryCocone : Cocone braidGroupDiagram where
  pt := GrpCat.of braid_group_inf
  ι :=
    NatTrans.ofSequence
      (app := fun n => GrpCat.ofHom (finiteToInfiniteGroupHom n))
      (naturality := by
        intro n
        apply GrpCat.hom_ext
        exact finiteToInfiniteGroupHom_succ_compatible n)

/-- Mathlib's categorical colimit object of the finite braid-group tower. -/
def braidGroupColimit : GrpCat :=
  colimit braidGroupDiagram

/-- Canonical comparison map from the categorical finite-stage colimit to the
repository-owned presented infinite braid group. -/
def groupFromColimit : braidGroupColimit ⟶ GrpCat.of braid_group_inf :=
  colimit.desc braidGroupBoundaryCocone

/-- The comparison map restricts on every finite stage to the canonical
`B_{n+1} → B_∞` embedding. -/
theorem groupFromColimit_ι (n : ℕ) :
    colimit.ι braidGroupDiagram n ≫ groupFromColimit =
      GrpCat.ofHom (finiteToInfiniteGroupHom n) := by
  exact colimit.ι_desc braidGroupBoundaryCocone n

/-- Elementwise stage readback of the group-colimit comparison map. -/
theorem groupFromColimit_ι_apply
    (n : ℕ) (g : braid_group (n + 1)) :
    groupFromColimit (colimit.ι braidGroupDiagram n g) =
      finiteToInfiniteGroupHom n g := by
  have h := congrArg
    (fun f => f g) (groupFromColimit_ι n)
  exact h

end InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
