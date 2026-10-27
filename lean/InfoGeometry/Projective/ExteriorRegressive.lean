/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Basis-normalized Hodge duality and the regressive product

The Hodge map is constructed from the signed complementary exterior basis.
Its same-grade basis pairing is the Kronecker pairing times the top blade.
The regressive product uses the actual inverse Hodge map, with the top blade
as unit. No duality or product law is assumed as a structure field.

This file does not assert that a nonzero regressive product represents every
intersection, or prove the homogeneous Hodge square formula.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorRegressive

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ}

/-- Complementation permutes the entire finite-set basis index. -/
def complementEquiv (n : ℕ) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun s := sᶜ
  invFun s := sᶜ
  left_inv s := compl_compl s
  right_inv s := compl_compl s

@[simp] theorem complementEquiv_apply (s : Finset (Fin n)) :
    complementEquiv n s = sᶜ := rfl

@[simp] theorem complementEquiv_symm_apply (s : Finset (Fin n)) :
    (complementEquiv n).symm s = sᶜ := rfl

/-- The sign of sorting the ordered concatenation of `s` and its complement. -/
def shuffleSign (s : Finset (Fin n)) : ℤˣ :=
  (Set.powersetCard.permOfDisjoint
    (s := Set.powersetCard.ofCard (s := s) rfl)
    (t := Set.powersetCard.ofCard (s := sᶜ) rfl)
    disjoint_compl_right).sign

/-- The shuffle sign as a unit of the coefficient field. -/
def orientationUnit (s : Finset (Fin n)) : Kˣ :=
  Units.map (Int.castRingHom K).toMonoidHom (shuffleSign s)

theorem orientationUnit_smul (s : Finset (Fin n)) (x : ExteriorAlgebra K V) :
    (orientationUnit (K := K) s : K) • x = shuffleSign s • x := by
  change (((shuffleSign s : ℤ) : K) • x) = (shuffleSign s : ℤ) • x
  exact Int.cast_smul_eq_zsmul K _ _

theorem orientationUnit_mul_self (s : Finset (Fin n)) :
    (orientationUnit (K := K) s : K) * (orientationUnit (K := K) s : K) = 1 := by
  have h : orientationUnit (K := K) s * orientationUnit (K := K) s = 1 := by
    unfold orientationUnit
    rw [← map_mul, Int.units_mul_self, map_one]
  exact congrArg (fun u : Kˣ => (u : K)) h

variable (b : Module.Basis (Fin n) K V)

/-- The oriented top blade of the chosen ordered basis. -/
def volume : ExteriorAlgebra K V := b.ExteriorAlgebra Finset.univ

theorem volume_ne_zero : volume b ≠ 0 := b.ExteriorAlgebra.ne_zero Finset.univ

@[simp] theorem basis_empty : b.ExteriorAlgebra ∅ = 1 := by
  simp [ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]

/-- Complementary basis blades multiply with their actual shuffle sign. -/
theorem basis_mul_compl (s : Finset (Fin n)) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra sᶜ =
      (orientationUnit (K := K) s : K) • volume b := by
  calc
    b.ExteriorAlgebra s * b.ExteriorAlgebra sᶜ =
        shuffleSign s • b.ExteriorAlgebra (s.disjUnion sᶜ disjoint_compl_right) := by
      simpa only [shuffleSign, Set.powersetCard.coe_disjUnion,
        Set.powersetCard.val_ofCard] using
        (ExteriorAlgebra.basis_mul_of_disjoint b
          (Set.powersetCard.ofCard (s := s) rfl)
          (Set.powersetCard.ofCard (s := sᶜ) rfl) disjoint_compl_right)
    _ = shuffleSign s • volume b := by
      simp only [Finset.disjUnion_eq_union, Finset.union_compl, volume]
    _ = (orientationUnit (K := K) s : K) • volume b :=
      (orientationUnit_smul s (volume b)).symm

/-- Constructed Hodge equivalence, rather than a supplied duality witness. -/
def hodge : ExteriorAlgebra K V ≃ₗ[K] ExteriorAlgebra K V :=
  b.ExteriorAlgebra.equiv
    ((b.ExteriorAlgebra.reindex (complementEquiv n)).unitsSMul (orientationUnit (K := K)))
    (Equiv.refl (Finset (Fin n)))

@[simp] theorem hodge_basis (s : Finset (Fin n)) :
    hodge b (b.ExteriorAlgebra s) =
      (orientationUnit (K := K) s : K) • b.ExteriorAlgebra sᶜ := by
  simp [hodge, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply, Units.smul_def]

/-- Diagonal Hodge pairing is the fixed top blade. -/
theorem basis_mul_hodge_self (s : Finset (Fin n)) :
    b.ExteriorAlgebra s * hodge b (b.ExteriorAlgebra s) = volume b := by
  rw [hodge_basis, mul_smul_comm, basis_mul_compl, smul_smul,
    orientationUnit_mul_self, one_smul]

/-- Distinct equal-degree basis blades have zero Hodge pairing. -/
theorem basis_mul_hodge_of_ne (s t : Finset (Fin n))
    (hcard : s.card = t.card) (hne : s ≠ t) :
    b.ExteriorAlgebra s * hodge b (b.ExteriorAlgebra t) = 0 := by
  have hnot : ¬Disjoint s tᶜ := by
    intro hd
    have hsub : s ⊆ t := disjoint_compl_right_iff.mp hd
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard.symm.le)
  have hmul : b.ExteriorAlgebra s * b.ExteriorAlgebra tᶜ = 0 := by
    simpa only [Set.powersetCard.val_ofCard] using
      (ExteriorAlgebra.basis_mul_of_not_disjoint b
        (Set.powersetCard.ofCard (s := s) rfl)
        (Set.powersetCard.ofCard (s := tᶜ) rfl) hnot)
  rw [hodge_basis, mul_smul_comm, hmul, smul_zero]

/-- Volume-normalized Hodge pairing on each homogeneous basis component. -/
theorem basis_hodge_pairing (s t : Finset (Fin n)) (hcard : s.card = t.card) :
    b.ExteriorAlgebra s * hodge b (b.ExteriorAlgebra t) =
      if s = t then volume b else 0 := by
  classical
  by_cases h : s = t
  · subst t
    rw [if_pos rfl, basis_mul_hodge_self]
  · rw [if_neg h]
    exact basis_mul_hodge_of_ne b s t hcard h

@[simp] theorem hodge_one : hodge b 1 = volume b := by
  have h := basis_mul_hodge_self b (∅ : Finset (Fin n))
  simpa only [basis_empty, one_mul] using h

@[simp] theorem hodge_volume : hodge b (volume b) = 1 := by
  have h := basis_mul_compl b (Finset.univ : Finset (Fin n))
  simp only [Finset.compl_univ, basis_empty, mul_one] at h
  have hc : (1 : K) =
      (orientationUnit (K := K) (Finset.univ : Finset (Fin n)) : K) := by
    apply smul_left_injective K (volume_ne_zero b)
    simpa only [one_smul] using h
  change hodge b (b.ExteriorAlgebra Finset.univ) = 1
  rw [hodge_basis, Finset.compl_univ, basis_empty, ← hc, one_smul]

@[simp] theorem hodge_symm_one : (hodge b).symm 1 = volume b := by
  apply (hodge b).injective
  simp only [LinearEquiv.apply_symm_apply, hodge_volume]

@[simp] theorem hodge_symm_volume : (hodge b).symm (volume b) = 1 := by
  apply (hodge b).injective
  simp only [LinearEquiv.apply_symm_apply, hodge_one]

/-- Regressive multiplication uses the actual inverse Hodge equivalence. -/
def regressive (a c : ExteriorAlgebra K V) : ExteriorAlgebra K V :=
  (hodge b).symm (hodge b a * hodge b c)

@[simp] theorem hodge_regressive (a c : ExteriorAlgebra K V) :
    hodge b (regressive b a c) = hodge b a * hodge b c := by
  simp only [regressive, LinearEquiv.apply_symm_apply]

theorem regressive_assoc (a c d : ExteriorAlgebra K V) :
    regressive b (regressive b a c) d = regressive b a (regressive b c d) := by
  apply (hodge b).injective
  simp only [hodge_regressive, mul_assoc]

@[simp] theorem volume_regressive (a : ExteriorAlgebra K V) :
    regressive b (volume b) a = a := by
  apply (hodge b).injective
  simp only [hodge_regressive, hodge_volume, one_mul]

@[simp] theorem regressive_volume (a : ExteriorAlgebra K V) :
    regressive b a (volume b) = a := by
  apply (hodge b).injective
  simp only [hodge_regressive, hodge_volume, mul_one]

@[simp] theorem zero_regressive (a : ExteriorAlgebra K V) :
    regressive b 0 a = 0 := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_zero, zero_mul]

@[simp] theorem regressive_zero (a : ExteriorAlgebra K V) :
    regressive b a 0 = 0 := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_zero, mul_zero]

theorem add_regressive (a c d : ExteriorAlgebra K V) :
    regressive b (a + c) d = regressive b a d + regressive b c d := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_add, add_mul]

theorem regressive_add (a c d : ExteriorAlgebra K V) :
    regressive b a (c + d) = regressive b a c + regressive b a d := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_add, mul_add]

theorem smul_regressive (r : K) (a c : ExteriorAlgebra K V) :
    regressive b (r • a) c = r • regressive b a c := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_smul, smul_mul_assoc]

theorem regressive_smul (r : K) (a c : ExteriorAlgebra K V) :
    regressive b a (r • c) = r • regressive b a c := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_smul, mul_smul_comm]

end InfoGeometry.Projective.ExteriorRegressive
