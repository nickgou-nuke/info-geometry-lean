import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
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
  have hijFin : i.succ = j.castSucc := Fin.ext hij
  have hab : i.castSucc ≠ i.succ := by
    simp [Fin.ext_iff]
  have hac : i.castSucc ≠ j.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have hcb : j.succ ≠ i.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ]
    omega
  dsimp [adjacentSwap]
  rw [← hijFin]
  calc
    _ = Equiv.swap i.castSucc j.succ := by
      simpa only [Equiv.swap_comm] using
        (Equiv.swap_mul_swap_mul_swap (y := i.succ) hcb hac.symm)
    _ = _ := by
      simpa only [Equiv.swap_comm] using
        (Equiv.swap_mul_swap_mul_swap hab hac).symm

/-- Far adjacent transpositions have disjoint supports and commute. -/
theorem adjacentSwap_far_commute
    (m : ℕ) (i j : Fin m)
    (hfar : i.val + 2 ≤ j.val) :
    adjacentSwap m i * adjacentSwap m j =
      adjacentSwap m j * adjacentSwap m i := by
  have h00 : j.castSucc ≠ i.castSucc := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]
    omega
  have h01 : j.castSucc ≠ i.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have h10 : j.succ ≠ i.castSucc := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have h11 : j.succ ≠ i.succ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ]
    omega
  dsimp [adjacentSwap]
  rw [Equiv.mul_swap_eq_swap_mul,
    Equiv.swap_apply_of_ne_of_ne h00 h01,
    Equiv.swap_apply_of_ne_of_ne h10 h11]

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
  apply MonoidHom.mrange_eq_top.mp
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
  simp [pow_two]

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

/-! ## Pure braid kernel readout -/

/-- The pure braid subgroup on `m+1` strands, defined intrinsically as the
kernel of the canonical permutation quotient. -/
def pureBraidSubgroup (m : ℕ) : Subgroup (braid_group (m + 1)) :=
  (braidToPerm m).ker

@[simp] theorem mem_pureBraidSubgroup_iff
    (m : ℕ) (g : braid_group (m + 1)) :
    g ∈ pureBraidSubgroup m ↔ braidToPerm m g = 1 :=
  Iff.rfl

/-- Every standard Artin generator square belongs to the pure braid kernel. -/
theorem generatorSquare_mem_pureBraidSubgroup
    (m : ℕ) (i : Fin m) :
    (σ' m i) ^ 2 ∈ pureBraidSubgroup m :=
  generatorSquare_mem_kernel m i

/-- Every conjugate of a standard generator square is pure. -/
theorem conjugate_generatorSquare_mem_pureBraidSubgroup
    (m : ℕ) (w : braid_group (m + 1)) (i : Fin m) :
    w * (σ' m i) ^ 2 * w⁻¹ ∈ pureBraidSubgroup m := by
  change braidToPerm m (w * (σ' m i) ^ 2 * w⁻¹) = 1
  simp only [map_mul, map_pow, map_inv, braidToPerm_generator]
  have hs : adjacentSwap m i ^ 2 = 1 := by
    simp [pow_two]
  rw [hs]
  simp

/-! ## The quotient by square relators

The square relators are known to lie in the permutation kernel.  Thus the
permutation map descends to their quotient.  Its kernel is exactly the image
of the pure braid kernel in that quotient; identifying this image with the
trivial subgroup is the remaining reverse-inclusion problem.
-/

/-- The permutation representation induced on the quotient by the normal
closure of the standard generator squares. -/
noncomputable def braidToPermModSquares (m : ℕ) :
    (braid_group (m + 1) ⧸ Subgroup.normalClosure (generatorSquares m)) →*
      Equiv.Perm (Fin (m + 1)) :=
  QuotientGroup.lift (Subgroup.normalClosure (generatorSquares m))
    (braidToPerm m) (normalClosure_generatorSquares_le_kernel m)

/-- The descended permutation representation remains surjective. -/
theorem braidToPermModSquares_surjective (m : ℕ) :
    Function.Surjective (braidToPermModSquares m) :=
  QuotientGroup.lift_surjective_of_surjective
    (Subgroup.normalClosure (generatorSquares m)) (braidToPerm m)
    (braidToPerm_surjective m)
    (normalClosure_generatorSquares_le_kernel m)

/-- The residual kernel after imposing generator squares is the image of the
pure braid subgroup.  This records the precise obstruction to proving that
the square-relator quotient is the symmetric group. -/
theorem ker_braidToPermModSquares (m : ℕ) :
    (braidToPermModSquares m).ker =
      Subgroup.map
        (QuotientGroup.mk'
          (Subgroup.normalClosure (generatorSquares m)))
        (pureBraidSubgroup m) := by
  simpa [braidToPermModSquares, pureBraidSubgroup] using
    (QuotientGroup.ker_lift
      (Subgroup.normalClosure (generatorSquares m))
      (braidToPerm m)
      (normalClosure_generatorSquares_le_kernel m))

/-- The square-relator quotient has no residual kernel exactly when the
normal closure of its relators is the full pure braid kernel. -/
theorem normalClosure_eq_pureBraid_iff_residual_kernel_trivial (m : ℕ) :
    Subgroup.normalClosure (generatorSquares m) = pureBraidSubgroup m ↔
      (braidToPermModSquares m).ker = ⊥ := by
  rw [ker_braidToPermModSquares, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (normalClosure_generatorSquares_le_kernel m) h

/-! ## Type A Coxeter target

The quotient by generator squares has the Coxeter relations of type A: adjacent
generators have Coxeter exponent three and nonadjacent generators exponent two.
The following Artin system makes the forward map to Mathlib's presented type A
Coxeter group explicit. -/

/-- The simple reflections of the type A Coxeter group satisfy the braid and
far-commutation relations required by the Artin presentation. -/
def typeACoxeterArtinSystem (m : ℕ) :
    ArtinBraidSystem (CoxeterMatrix.Aₙ m).Group m where
  gen i := (CoxeterMatrix.Aₙ m).simple i
  adjacent i j hij := by
    let cs := (CoxeterMatrix.Aₙ m).toCoxeterSystem
    have hM : (CoxeterMatrix.Aₙ m) i j = 3 := by
      by_cases heq : i = j
      · subst j
        omega
      · simp [CoxeterMatrix.Aₙ, heq, hij]
    have hpow : (cs.simple i * cs.simple j) ^ 3 = 1 := by
      have h := cs.simple_mul_simple_pow i j
      rw [hM] at h
      exact h
    have hword : cs.simple i * cs.simple j * cs.simple i *
        cs.simple j * cs.simple i * cs.simple j = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hpow
    have hPQ : (cs.simple i * cs.simple j * cs.simple i) *
        (cs.simple j * cs.simple i * cs.simple j)⁻¹ =
          cs.simple i * cs.simple j * cs.simple i * cs.simple j * cs.simple i * cs.simple j := by
      simp [CoxeterSystem.inv_simple, mul_assoc]
    calc
      cs.simple i * cs.simple j * cs.simple i =
          (cs.simple i * cs.simple j * cs.simple i) *
            (cs.simple j * cs.simple i * cs.simple j)⁻¹ *
            (cs.simple j * cs.simple i * cs.simple j) := by group
      _ = (cs.simple i * cs.simple j * cs.simple i *
            cs.simple j * cs.simple i * cs.simple j) *
            (cs.simple j * cs.simple i * cs.simple j) := by rw [hPQ]
      _ = cs.simple j * cs.simple i * cs.simple j := by rw [hword]; simp
  farCommute i j hfar := by
    let cs := (CoxeterMatrix.Aₙ m).toCoxeterSystem
    have hM : (CoxeterMatrix.Aₙ m) i j = 2 := by
      have hne : i ≠ j := by
        intro h
        subst j
        omega
      simp only [CoxeterMatrix.Aₙ, Matrix.of_apply]
      simp only [if_neg hne]
      split_ifs <;> omega
    have hpow : (cs.simple i * cs.simple j) ^ 2 = 1 := by
      have h := cs.simple_mul_simple_pow i j
      rw [hM] at h
      exact h
    have hprod : (cs.simple i * cs.simple j) * (cs.simple i * cs.simple j) = 1 := by
      simpa [pow_two] using hpow
    calc
      cs.simple i * cs.simple j = (cs.simple i * cs.simple j)⁻¹ :=
        eq_inv_of_mul_eq_one_left hprod
      _ = cs.simple j * cs.simple i := by simp [CoxeterSystem.inv_simple]

/-- The type A Coxeter representation of the Artin braid group. -/
def braidToTypeACoxeter (m : ℕ) :
    braid_group (m + 1) →* (CoxeterMatrix.Aₙ m).Group :=
  (typeACoxeterArtinSystem m).toGroupHom

@[simp] theorem braidToTypeACoxeter_generator (m : ℕ) (i : Fin m) :
    braidToTypeACoxeter m (σ' m i) = (CoxeterMatrix.Aₙ m).simple i := by
  exact ArtinBraidSystem.toGroupHom_generator (typeACoxeterArtinSystem m) i

/-- The square relators vanish in the type A Coxeter representation. -/
theorem generatorSquare_mem_typeACoxeter_kernel (m : ℕ) (i : Fin m) :
    (σ' m i) ^ 2 ∈ (braidToTypeACoxeter m).ker := by
  change braidToTypeACoxeter m ((σ' m i) ^ 2) = 1
  rw [map_pow, braidToTypeACoxeter_generator]
  exact CoxeterSystem.simple_sq ((CoxeterMatrix.Aₙ m).toCoxeterSystem) i

/-- The type A Coxeter representation factors through the quotient by
generator-square relators. -/
noncomputable def braidToTypeACoxeterModSquares (m : ℕ) :
    (braid_group (m + 1) ⧸ Subgroup.normalClosure (generatorSquares m)) →*
      (CoxeterMatrix.Aₙ m).Group :=
  QuotientGroup.lift (Subgroup.normalClosure (generatorSquares m))
    (braidToTypeACoxeter m) (by
      apply Subgroup.normalClosure_le_normal
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact generatorSquare_mem_typeACoxeter_kernel m i)

@[simp] theorem braidToTypeACoxeterModSquares_generator (m : ℕ) (i : Fin m) :
    braidToTypeACoxeterModSquares m
      (QuotientGroup.mk'
        (Subgroup.normalClosure (generatorSquares m)) (σ' m i)) =
      (CoxeterMatrix.Aₙ m).simple i := by
  simp [braidToTypeACoxeterModSquares]

/-- The induced map from the square-relator quotient reaches every element of
the type A Coxeter group, since its simple reflections are images of braid
generators. -/
theorem braidToTypeACoxeterModSquares_surjective (m : ℕ) :
    Function.Surjective (braidToTypeACoxeterModSquares m) := by
  apply MonoidHom.mrange_eq_top.mp
  apply top_unique
  rw [← (CoxeterMatrix.Aₙ m).toCoxeterSystem.submonoid_closure_range_simple]
  apply Submonoid.closure_le.2
  rintro g ⟨i, rfl⟩
  exact ⟨QuotientGroup.mk'
    (Subgroup.normalClosure (generatorSquares m)) (σ' m i),
    braidToTypeACoxeterModSquares_generator m i⟩

private theorem product_cube_eq_one_of_artin_involutions
    {G : Type*} [Group G] (x y : G)
    (hx : x * x = 1) (hy : y * y = 1)
    (hxyx : x * y * x = y * x * y) :
    (x * y) ^ 3 = 1 := by
  calc
    (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
      simp only [pow_succ, pow_two]
      group
    _ = (y * x * y) * (y * x * y) := by rw [hxyx]
    _ = y * x * (y * y) * x * y := by group
    _ = 1 := by rw [hy, hx]; simp

private theorem product_square_eq_one_of_commuting_involutions
    {G : Type*} [Group G] (x y : G)
    (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) :
    (x * y) ^ 2 = 1 := by
  calc
    (x * y) ^ 2 = x * y * x * y := by simp only [pow_two]; group
    _ = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy.symm]
    _ = 1 := by simp [mul_assoc, hx, hy]

private theorem adjacentSwap_cubed_eq_one
    (m : ℕ) (i j : Fin m) (hij : i.val + 1 = j.val) :
    (adjacentSwap m i * adjacentSwap m j) ^ 3 = 1 := by
  apply product_cube_eq_one_of_artin_involutions
    (adjacentSwap m i) (adjacentSwap m j)
  · simpa [pow_two] using adjacentSwap_sq m i
  · simpa [pow_two] using adjacentSwap_sq m j
  · exact adjacentSwap_braid m i j hij

private theorem adjacentSwap_cubed_eq_one_of_reverse
    (m : ℕ) (i j : Fin m) (hij : j.val + 1 = i.val) :
    (adjacentSwap m i * adjacentSwap m j) ^ 3 = 1 := by
  have hrev := adjacentSwap_cubed_eq_one m j i hij
  have hi : adjacentSwap m i * adjacentSwap m i = 1 := by
    simpa [pow_two] using adjacentSwap_sq m i
  have hj : adjacentSwap m j * adjacentSwap m j = 1 := by
    simpa [pow_two] using adjacentSwap_sq m j
  calc
    (adjacentSwap m i * adjacentSwap m j) ^ 3 =
        adjacentSwap m j * ((adjacentSwap m j * adjacentSwap m i) ^ 3) *
          adjacentSwap m j := by
            simp [pow_succ, pow_two, mul_assoc, hi, hj]
    _ = 1 := by rw [hrev, hj]; simp

/-- The adjacent transpositions satisfy the Coxeter relations of type A. -/
private def typeACoxeterLiftable (m : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.Aₙ m) (adjacentSwap m) := by
  intro i j
  change (adjacentSwap m i * adjacentSwap m j) ^
    (CoxeterMatrix.Aₙ m) i j = 1
  by_cases hij : i = j
  · subst j
    simp [pow_one, adjacentSwap_sq]
  · by_cases hforward : i.val + 1 = j.val
    · have hentry : (CoxeterMatrix.Aₙ m) i j = 3 := by
        simp [CoxeterMatrix.Aₙ, hij, hforward]
      rw [hentry]
      exact adjacentSwap_cubed_eq_one m i j hforward
    · by_cases hbackward : j.val + 1 = i.val
      · have hentry : (CoxeterMatrix.Aₙ m) i j = 3 := by
          simp [CoxeterMatrix.Aₙ, hij, hforward, hbackward]
        rw [hentry]
        exact adjacentSwap_cubed_eq_one_of_reverse m i j hbackward
      · have hentry : (CoxeterMatrix.Aₙ m) i j = 2 := by
          simp [CoxeterMatrix.Aₙ, hij, hforward, hbackward]
        rw [hentry]
        have hfar : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val := by omega
        rcases hfar with h | h
        · exact product_square_eq_one_of_commuting_involutions
            (adjacentSwap m i) (adjacentSwap m j)
            (by simpa [pow_two] using adjacentSwap_sq m i)
            (by simpa [pow_two] using adjacentSwap_sq m j)
            (adjacentSwap_far_commute m i j h)
        · exact product_square_eq_one_of_commuting_involutions
            (adjacentSwap m i) (adjacentSwap m j)
            (by simpa [pow_two] using adjacentSwap_sq m i)
            (by simpa [pow_two] using adjacentSwap_sq m j)
            ((adjacentSwap_far_commute m j i h).symm)

/-- The adjacent transpositions satisfy the Coxeter relations of type A.
This is the canonical realization map from Mathlib's presented Coxeter group
to the symmetric group. -/
def typeACoxeterToPerm (m : ℕ) :
    (CoxeterMatrix.Aₙ m).Group →* Equiv.Perm (Fin (m + 1)) :=
  (CoxeterMatrix.Aₙ m).toCoxeterSystem.lift ⟨adjacentSwap m,
    typeACoxeterLiftable m⟩

@[simp] theorem typeACoxeterToPerm_simple (m : ℕ) (i : Fin m) :
    typeACoxeterToPerm m ((CoxeterMatrix.Aₙ m).simple i) =
      adjacentSwap m i := by
  exact CoxeterSystem.lift_apply_simple
    (CoxeterMatrix.Aₙ m).toCoxeterSystem
    (typeACoxeterLiftable m) i

theorem typeACoxeterToPerm_surjective (m : ℕ) :
    Function.Surjective (typeACoxeterToPerm m) := by
  apply MonoidHom.mrange_eq_top.mp
  apply top_unique
  rw [← Equiv.Perm.mclosure_swap_castSucc_succ m]
  apply Submonoid.closure_le.2
  rintro p ⟨i, rfl⟩
  exact ⟨(CoxeterMatrix.Aₙ m).simple i, typeACoxeterToPerm_simple m i⟩

/-- The type-A Coxeter realization commutes with the canonical braid
permutation representation on every Artin generator. -/
theorem braidToPerm_eq_typeACoxeter_comp (m : ℕ) :
    braidToPerm m = (typeACoxeterToPerm m).comp (braidToTypeACoxeter m) := by
  change (permutationArtinSystem m).toGroupHom = _
  symm
  apply ArtinBraidSystem.toGroupHom_unique (permutationArtinSystem m)
  intro i
  simp [braidToPerm_generator, braidToTypeACoxeter_generator,
    typeACoxeterToPerm_simple]

end InfoGeometry.Categorical.BraidPermutationQuotient
