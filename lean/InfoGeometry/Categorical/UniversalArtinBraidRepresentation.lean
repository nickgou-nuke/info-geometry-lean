import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic

import proofs.BraidProject.BraidGroup

/-!
# Universal finite Artin braid-group representation

This module is the canonical universal mapping layer for the repository's
finite braid groups.

Rather than parameterizing by the number of strands and repeatedly reasoning
about `n - 1`, the datum is indexed by the number `m` of Artin generators.
An `ArtinBraidSystem G m` therefore lifts canonically to

`Braid.braid_group (m + 1) →* G`.

The laws are exactly those in `Braid.braid_rels m`:

* adjacent braid:
  `T_i T_{i+1} T_i = T_{i+1} T_i T_{i+1}`;
* far commutativity:
  `T_i T_j = T_j T_i` when `i + 2 ≤ j`.

No model-specific representation is introduced here.
-/

namespace InfoGeometry.Categorical.UniversalArtinBraidRepresentation

open Braid

/-- A finite Artin braid-generator system in an arbitrary target group.

The index `m` is the number of generators, so this data represents
`B_{m+1}`. -/
structure ArtinBraidSystem (G : Type*) [Group G] (m : ℕ) where
  gen : Fin m → G
  adjacent :
    ∀ (i j : Fin m), i.val + 1 = j.val →
      gen i * gen j * gen i = gen j * gen i * gen j
  farCommute :
    ∀ (i j : Fin m), i.val + 2 ≤ j.val →
      gen i * gen j = gen j * gen i

namespace ArtinBraidSystem

variable {G : Type*} [Group G] {m : ℕ}

/-- Evaluation of a braid relator in a target group once the corresponding
Artin relation is known. -/
theorem braid_rel_lift_eq_one
    (sys : ArtinBraidSystem G m)
    (i j : Fin m)
    (hij : i.val + 1 = j.val) :
    FreeGroup.lift sys.gen (braid_rel i j) = 1 := by
  simp only [braid_rel, map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [sys.adjacent i j hij]
  simp [mul_assoc]

/-- Evaluation of a far-commutativity relator in the target group. -/
theorem comm_rel_lift_eq_one
    (sys : ArtinBraidSystem G m)
    (i j : Fin m)
    (hij : i.val + 2 ≤ j.val) :
    FreeGroup.lift sys.gen (comm_rel i j) = 1 := by
  simp only [comm_rel, map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [sys.farCommute i j hij]
  simp [mul_assoc]

/-- Every defining relation of `B_{m+1}` evaluates to the identity. -/
theorem respects_braid_rels
    (sys : ArtinBraidSystem G m) :
    ∀ r ∈ braid_rels m, FreeGroup.lift sys.gen r = 1 := by
  cases m with
  | zero =>
      intro r hr
      simp [braid_rels] at hr
  | succ m =>
      cases m with
      | zero =>
          intro r hr
          simp [braid_rels] at hr
      | succ n =>
          intro r hr
          change
            (∃ i : Fin (n + 1), r = braid_rel i.castSucc i.succ) ∨
              (∃ i j : Fin n, i ≤ j ∧
                r = comm_rel i.castSucc.castSucc j.succ.succ) at hr
          rcases hr with hAdj | hFar
          · rcases hAdj with ⟨i, rfl⟩
            apply braid_rel_lift_eq_one sys
            rfl
          · rcases hFar with ⟨i, j, hij, rfl⟩
            apply comm_rel_lift_eq_one sys
            omega

/-- Universal homomorphism from the repository's canonical finite braid group
to any group carrying an Artin braid system. -/
def toGroupHom
    (sys : ArtinBraidSystem G m) :
    braid_group (m + 1) →* G := by
  change PresentedGroup (braid_rels m) →* G
  exact PresentedGroup.toGroup sys.respects_braid_rels

@[simp] theorem toGroupHom_generator
    (sys : ArtinBraidSystem G m)
    (i : Fin m) :
    sys.toGroupHom (σ' m i) = sys.gen i := by
  change PresentedGroup.toGroup sys.respects_braid_rels
      (PresentedGroup.of i) = sys.gen i
  exact PresentedGroup.toGroup.of sys.respects_braid_rels

/-- Universal uniqueness: a homomorphism out of `B_{m+1}` is determined by
its values on the standard Artin generators. -/
theorem toGroupHom_unique
    (sys : ArtinBraidSystem G m)
    (φ : braid_group (m + 1) →* G)
    (hφ : ∀ i : Fin m, φ (σ' m i) = sys.gen i) :
    φ = sys.toGroupHom := by
  change
    φ =
      PresentedGroup.toGroup sys.respects_braid_rels
  apply PresentedGroup.ext
  intro i
  rw [PresentedGroup.toGroup.of]
  exact hφ i

/-- Composition with a group homomorphism transports an Artin braid system. -/
def map
    {H : Type*} [Group H]
    (sys : ArtinBraidSystem G m)
    (f : G →* H) :
    ArtinBraidSystem H m where
  gen i := f (sys.gen i)
  adjacent i j hij := by
    simpa using congrArg f (sys.adjacent i j hij)
  farCommute i j hij := by
    simpa using congrArg f (sys.farCommute i j hij)

/-- Functoriality of the universal lift under postcomposition. -/
theorem map_toGroupHom
    {H : Type*} [Group H]
    (sys : ArtinBraidSystem G m)
    (f : G →* H) :
    (sys.map f).toGroupHom = f.comp sys.toGroupHom := by
  apply PresentedGroup.ext
  intro i
  simp [map]

end ArtinBraidSystem

end InfoGeometry.Categorical.UniversalArtinBraidRepresentation
