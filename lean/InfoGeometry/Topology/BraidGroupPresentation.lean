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
def braid_group_inf := PresentedGroup braid_rels_inf

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
  simp [braid_rels, braid_rel, mul_assoc]

theorem braid_group_inf.braid (i : ℕ) :
    σi i * σi i.succ * σi i = σi i.succ * σi i * σi i.succ := by
  symm
  rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left
  use i
  simp [braid_rels, braid_rel, mul_assoc]

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
    simp [braid_rels, comm_rel, mul_assoc]

theorem braid_group_inf.comm {i j : ℕ} (h : i + 2 ≤ j) :
    σi i * σi j = σi j * σi i := by
  symm
  rw [← mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  right
  simp
  use i, j, h
  simp [comm_rel, mul_assoc]

end Braid
