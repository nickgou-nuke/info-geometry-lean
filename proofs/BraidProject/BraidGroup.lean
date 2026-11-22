/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Fin.Basic

namespace Braid

section
local instance (S : Type _) : Coe S (FreeGroup S) := ⟨FreeGroup.of⟩

def comm_rel {S : Type*} (i j : S) : FreeGroup S :=
  i * j * (↑i)⁻¹ * (↑j)⁻¹

def braid_rel {S : Type*} (i j : S) : FreeGroup S :=
  i * j * i * (↑j)⁻¹ * (↑i)⁻¹ * (↑j)⁻¹

end

def braid_rels : (n : ℕ) → Set (FreeGroup (Fin n))
  | 0 => ∅
  | 1 => ∅
  | n + 2 =>
    {r | ∃ i : Fin (n + 1), r = braid_rel i.castSucc i.succ} ∪
    {r | ∃ i j : Fin n, i ≤ j ∧ r = comm_rel i.castSucc.castSucc j.succ.succ}

def braid_rels_inf : Set (FreeGroup ℕ) :=
  {r | ∃ i : ℕ, r = .of i * (.of (i + 1)) * .of i *
    (.of (i + 1))⁻¹ * (.of i)⁻¹ * (.of (i + 1))⁻¹} ∪
  {r | ∃ i j : ℕ, i + 2 ≤ j ∧ r = .of i * .of j * (.of i)⁻¹ * (.of j)⁻¹}

def braid_group (n : ℕ) := PresentedGroup (braid_rels n.pred)
abbrev braid_group_inf := PresentedGroup braid_rels_inf

instance (n : ℕ) : Group (braid_group n) := by
  unfold braid_group
  infer_instance

instance : Group braid_group_inf := by
  unfold braid_group_inf
  infer_instance

def braid_group.rel := PresentedGroup braid_rels_inf

def σ {n : ℕ} (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k
def σi (k : ℕ) : braid_group_inf := PresentedGroup.of k
abbrev σ' (n : ℕ) (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

theorem braid_group.braid {n : ℕ} (i : Fin (n + 1)) :
    σ' (n + 2) i.castSucc * σ i.succ * σ' (n + 2) i.castSucc =
      σ i.succ * σ' (n + 2) i.castSucc * σ i.succ := by
  symm
  rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left
  use i
  simp [braid_rel, mul_assoc]

theorem braid_group_inf.braid (i : ℕ) :
    σi i * σi i.succ * σi i = σi i.succ * σi i * σi i.succ := by
  symm
  rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left
  use i
  simp [mul_assoc]

theorem braid_group.comm {n : ℕ} {i j : Fin n} (h : i ≤ j) :
    σ' (n + 2) i.castSucc.castSucc * σ j.succ.succ =
      σ j.succ.succ * σ i.castSucc.castSucc := by
  symm
  rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  cases n
  · exact i.elim0
  · right
    use i, j, h
    simp [comm_rel, mul_assoc]

theorem braid_group_inf.comm {i j : ℕ} (h : i + 2 ≤ j) :
    σi i * σi j = σi j * σi i := by
  symm
  rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  right
  simp
  use i, j, h
  simp [mul_assoc]


noncomputable def braid_group.toGroup
    {n : ℕ} {G : Type*} [Group G]
    (f : Fin n → G)
    (hrels : ∀ r ∈ braid_rels n, FreeGroup.lift f r = 1) :
    braid_group (n + 1) →* G := by
  change PresentedGroup (braid_rels n) →* G
  exact PresentedGroup.toGroup (f := f) hrels

@[simp] theorem braid_group.toGroup_sigma
    {n : ℕ} {G : Type*} [Group G] (f : Fin n → G)
    (hrels : ∀ r ∈ braid_rels n, FreeGroup.lift f r = 1) (i : Fin n) :
    braid_group.toGroup f hrels (σ' n i) = f i := by
  exact PresentedGroup.toGroup.of hrels

theorem braid_group.toGroup_unique
    {n : ℕ} {G : Type*} [Group G] (f : Fin n → G)
    (hrels : ∀ r ∈ braid_rels n, FreeGroup.lift f r = 1)
    (φ : braid_group (n + 1) →* G) (hφ : ∀ i : Fin n, φ (σ' n i) = f i) :
    φ = braid_group.toGroup f hrels := by
  apply PresentedGroup.ext
  intro i
  exact (hφ i).trans (braid_group.toGroup_sigma f hrels i).symm

noncomputable def braid_group_inf.toGroup
    {G : Type*} [Group G] (f : ℕ → G)
    (hrels : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1) :
    braid_group_inf →* G :=
  PresentedGroup.toGroup (f := f) hrels

@[simp] theorem braid_group_inf.toGroup_sigma
    {G : Type*} [Group G] (f : ℕ → G)
    (hrels : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1) (i : ℕ) :
    braid_group_inf.toGroup f hrels (σi i) = f i := by
  exact PresentedGroup.toGroup.of hrels

theorem braid_group_inf.toGroup_unique
    {G : Type*} [Group G] (f : ℕ → G)
    (hrels : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1)
    (φ : braid_group_inf →* G) (hφ : ∀ i : ℕ, φ (σi i) = f i) :
    φ = braid_group_inf.toGroup f hrels := by
  apply PresentedGroup.ext
  intro i
  exact (hφ i).trans (braid_group_inf.toGroup_sigma f hrels i).symm

structure braid_group.HomData (n : ℕ) (G : Type*) [Group G] where
  generator : Fin n → G
  adjacent : ∀ (i j : Fin n), j.val = i.val + 1 →
    generator i * generator j * generator i = generator j * generator i * generator j
  far_commute : ∀ (i j : Fin n), i.val + 2 ≤ j.val →
    generator i * generator j = generator j * generator i

namespace braid_group.HomData

theorem relations {n : ℕ} {G : Type*} [Group G] (d : braid_group.HomData n G) :
    ∀ r ∈ braid_rels n, FreeGroup.lift d.generator r = 1 := by
  intro r hr
  cases n with
  | zero => simp [braid_rels] at hr
  | succ n =>
    cases n with
    | zero => simp [braid_rels] at hr
    | succ n =>
      have hrels : (∃ i : Fin (n + 1), r = braid_rel (i.castSucc) (i.succ)) ∨
          (∃ i j : Fin n, i ≤ j ∧ r = comm_rel (i.castSucc.castSucc) (j.succ.succ)) := by
        simpa only [braid_rels, Set.mem_union, Set.mem_setOf_eq] using hr
      rcases hrels with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
      · have hArtin := d.adjacent i.castSucc i.succ (by rfl)
        simp only [braid_rel, map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [hArtin]
        simp [mul_assoc]
      · have hsep : (i.castSucc.castSucc : Fin (n + 2)).val + 2 ≤
            (j.succ.succ : Fin (n + 2)).val := by simpa using Nat.add_le_add_right hij 2
        have hcomm := d.far_commute i.castSucc.castSucc j.succ.succ hsep
        simp only [comm_rel, map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [hcomm]
        simp [mul_assoc]

noncomputable def toGroupHom {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G) : braid_group (n + 1) →* G :=
  braid_group.toGroup d.generator d.relations

@[simp] theorem toGroupHom_sigma {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G) (i : Fin n) :
    d.toGroupHom (σ' n i) = d.generator i :=
  braid_group.toGroup_sigma d.generator d.relations i

theorem toGroupHom_unique {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G) (φ : braid_group (n + 1) →* G)
    (hφ : ∀ i : Fin n, φ (σ' n i) = d.generator i) :
    φ = d.toGroupHom :=
  braid_group.toGroup_unique d.generator d.relations φ hφ

end braid_group.HomData

end Braid
