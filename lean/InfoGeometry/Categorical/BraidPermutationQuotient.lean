import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

import InfoGeometry.Categorical.UniversalArtinBraidRepresentation
import proofs.BraidProject.BraidGroup

/-!
# Canonical finite braid-to-permutation quotient

For `m` Artin generators this module constructs the canonical homomorphism

  B_{m+1} → S_{m+1}

sending the i-th braid generator to the adjacent transposition
`swap i.castSucc i.succ`.

The construction reuses `UniversalArtinBraidRepresentation.ArtinBraidSystem`,
so there is a single presentation engine for all finite braid representations.

Closed here:
* adjacent swaps satisfy the Artin braid relation;
* disjoint adjacent swaps commute;
* the universal homomorphism exists;
* the homomorphism is surjective, using Mathlib's theorem that adjacent
  transpositions generate the finite symmetric group;
* the normal closure of all generator squares lies in the kernel.

Open downstream:
* equality of the kernel with that normal closure;
* equivalence with the repository's independent pure-braid presentation.
-/

namespace InfoGeometry.Categorical.BraidPermutationQuotient

open Braid
open InfoGeometry.Categorical.UniversalArtinBraidRepresentation

/-- The canonical adjacent transposition attached to the i-th Artin generator
of `B_{m+1}`. -/
def adjacentSwap (m : ℕ) (i : Fin m) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap i.castSucc i.succ

@[simp] theorem adjacentSwap_sq (m : ℕ) (i : Fin m) :
    adjacentSwap m i * adjacentSwap m i = 1 := by
  exact Equiv.swap_mul_self i.castSucc i.succ

/-- Adjacent transpositions satisfy the length-three Artin relation. -/
theorem adjacentSwap_braid
    (m : ℕ) (i j : Fin m)
    (hij : i.val + 1 = j.val) :
    adjacentSwap m i * adjacentSwap m j * adjacentSwap m i =
      adjacentSwap m j * adjacentSwap m i * adjacentSwap m j := by
  apply Equiv.ext
  intro x
  simp only [adjacentSwap, Equiv.Perm.mul_apply]
  by_cases hxi : x = i.castSucc
  · subst x
    simp
    apply Fin.ext
    omega
  · by_cases hxip : x = i.succ
    · subst x
      simp
      apply Fin.ext
      omega
    · by_cases hxj : x = j.succ
      · subst x
        simp
        apply Fin.ext
        omega
      · have hijFin : i.succ = j.castSucc := by
          apply Fin.ext
          exact hij
        simp [hxi, hxip, hxj, hijFin]

/-- Far adjacent transpositions have disjoint supports and commute. -/
theorem adjacentSwap_far_commute
    (m : ℕ) (i j : Fin m)
    (hfar : i.val + 2 ≤ j.val) :
    adjacentSwap m i * adjacentSwap m j =
      adjacentSwap m j * adjacentSwap m i := by
  apply Equiv.ext
  intro x
  simp only [adjacentSwap, Equiv.Perm.mul_apply]
  by_cases hxi : x = i.castSucc
  · subst x
    have hne1 : i.succ ≠ j.castSucc := by
      intro h
      have := congrArg Fin.val h
      omega
    have hne2 : i.succ ≠ j.succ := by
      intro h
      have := congrArg Fin.val h
      omega
    simp [hne1, hne2]
  · by_cases hxip : x = i.succ
    · subst x
      have hne0 : i.succ ≠ j.castSucc := by
        intro h
        have := congrArg Fin.val h
        omega
      have hne1 : i.castSucc ≠ j.castSucc := by
        intro h
        have := congrArg Fin.val h
        omega
      have hne2 : i.castSucc ≠ j.succ := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [hne0, hne1, hne2]
    · by_cases hxj : x = j.castSucc
      · subst x
        have hne0 : j.castSucc ≠ i.castSucc := by
          intro h
          have := congrArg Fin.val h
          omega
        have hne1 : j.castSucc ≠ i.succ := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [hne0, hne1]
      · by_cases hxjp : x = j.succ
        · subst x
          have hne0 : j.succ ≠ i.castSucc := by
            intro h
            have := congrArg Fin.val h
            omega
          have hne1 : j.succ ≠ i.succ := by
            intro h
            have := congrArg Fin.val h
            omega
          simp [hne0, hne1]
        · simp [hxi, hxip, hxj, hxjp]

/-- Adjacent transpositions form an Artin braid system. -/
def permutationArtinSystem (m : ℕ) :
    ArtinBraidSystem (Equiv.Perm (Fin (m + 1))) m where
  gen := adjacentSwap m
  adjacent := adjacentSwap_braid m
  farCommute := adjacentSwap_far_commute m

/-- Canonical permutation quotient `B_{m+1} → S_{m+1}`. -/
def braidToPerm (m : ℕ) :
    braid_group (m + 1) →* Equiv.Perm (Fin (m + 1)) :=
  (permutationArtinSystem m).toGroupHom

@[simp] theorem braidToPerm_generator (m : ℕ) (i : Fin m) :
    braidToPerm m (σ' m i) = adjacentSwap m i := by
  exact ArtinBraidSystem.toGroupHom_generator (permutationArtinSystem m) i

/-- The canonical finite braid-to-permutation map is surjective. -/
theorem braidToPerm_surjective (m : ℕ) :
    Function.Surjective (braidToPerm m) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← Equiv.Perm.mclosure_swap_castSucc_succ m]
  apply Submonoid.closure_le.2
  rintro g ⟨i, rfl⟩
  exact ⟨σ' m i, braidToPerm_generator m i⟩

/-- Set of square relators of the standard Artin generators. -/
def generatorSquares (m : ℕ) : Set (braid_group (m + 1)) :=
  {x | ∃ i : Fin m, x = (σ' m i) ^ 2}

/-- Every standard generator square lies in the permutation kernel. -/
theorem generatorSquare_mem_kernel
    (m : ℕ) (i : Fin m) :
    (σ' m i) ^ 2 ∈ (braidToPerm m).ker := by
  change braidToPerm m ((σ' m i) ^ 2) = 1
  rw [map_pow, braidToPerm_generator]
  simpa [pow_two] using adjacentSwap_sq m i

/-- The normal closure of generator squares is contained in the kernel of the
canonical permutation quotient. -/
theorem normalClosure_generatorSquares_le_kernel
    (m : ℕ) :
    Subgroup.normalClosure (generatorSquares m) ≤
      (braidToPerm m).ker := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact generatorSquare_mem_kernel m i

end InfoGeometry.Categorical.BraidPermutationQuotient
