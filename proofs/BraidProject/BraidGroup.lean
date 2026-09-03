import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Fin.Basic
import proofs.BraidProject.BraidMonoid

--set_option autoImplicit false
namespace Braid

section
local instance (S : Type _) : Coe S (FreeGroup S) := ⟨FreeGroup.of⟩

def comm_rel {S : Type _} (i j : S) : FreeGroup S :=
  i * j * (↑i)⁻¹ * (↑j)⁻¹

def braid_rel {S : Type _} (i j : S) : FreeGroup S :=
  i * j * i * (↑j)⁻¹ * (↑i)⁻¹ * (↑j)⁻¹

end

def braid_rels : (n : ℕ) → Set (FreeGroup (Fin n))
  | 0     => ∅
  | 1     => ∅
  | n + 2 =>
    { r | ∃ i : Fin (n + 1), r = braid_rel (i.castSucc) (i.succ) } ∪
    { r | ∃ i j : Fin n, i ≤ j ∧ r = comm_rel (i.castSucc.castSucc) (j.succ.succ) }

def braid_rels_inf : Set (FreeGroup ℕ) :=
  { r | ∃ i : ℕ , r = .of i * (.of (i + 1)) * .of i *
    (.of (i + 1))⁻¹ * (.of i)⁻¹ * (.of (i + 1))⁻¹} ∪
  { r | ∃ i j : ℕ, i + 2 ≤ j ∧ r = .of i * .of j * (.of i)⁻¹ * (.of j)⁻¹}

/-
The predecessor in the next definition is annoying, but hopefully not too bad.
Most of the time we will write `braid_group (n + 1)`, which corresponds to `B_{n + 1}`.
-/

def braid_group (n : ℕ) := PresentedGroup (braid_rels n.pred)

def braid_group_inf := PresentedGroup braid_rels_inf

instance (n : ℕ) : Group (braid_group n) := by
  unfold braid_group; infer_instance

instance : Group braid_group_inf := by
  unfold braid_group_inf; infer_instance

def braid_group.rel := PresentedGroup braid_rels_inf

def σ {n : ℕ} (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

def σi (k : ℕ) : braid_group_inf := PresentedGroup.of k


/-
This version makes n explicit. Note that `σ' n k` is an element of
`braid group (n + 1).`
-/
abbrev σ' (n : ℕ) (k : Fin n) : braid_group (n + 1) := PresentedGroup.of k

theorem braid_group.braid {n : ℕ} (i : Fin (n + 1)) :
    σ' (n + 2) i.castSucc * σ i.succ * σ' (n + 2) i.castSucc =
      σ i.succ * σ' (n + 2) i.castSucc * σ i.succ := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left; use i
  simp [braid_rels, braid_rel, mul_assoc]

theorem braid_group_inf.braid (i : ℕ) :
    σi i * σi i.succ * σi i = σi i.succ * σi i * σi i.succ := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  left; use i
  simp [braid_rels, braid_rel, mul_assoc]

theorem braid_group.comm {n : ℕ} {i j : Fin n} (h : i ≤ j) :
    σ' (n + 2) i.castSucc.castSucc * σ j.succ.succ = σ j.succ.succ * σ i.castSucc.castSucc := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  cases n
  . next => apply i.elim0
  . next n =>
    right; use i, j, h; simp [braid_rels, comm_rel, mul_assoc]

theorem braid_group_inf.comm {i j : ℕ} (h : i + 2 ≤ j) :
    σi i * σi j = σi j * σi i := by
  symm; rw [←mul_inv_eq_one]
  apply QuotientGroup.eq.mpr
  apply Subgroup.subset_normalClosure
  right
  simp
  use i
  use j
  constructor
  · exact h
  simp only [mul_assoc]

theorem generated_by (n : ℕ) (H : Subgroup (braid_group (n + 1))) (h : ∀ i : Fin n, σ' n i ∈ H) :
    ∀ x : braid_group (n + 1), x ∈ H := by
  intro x
  apply QuotientGroup.induction_on
  intro z
  change ⟦z⟧ ∈ H
  apply FreeGroup.induction_on (C := fun z => ⟦z⟧ ∈ H) _ (one_mem H) (fun _ => h _)
  . intro i
    change σ i ∈ H.carrier → (σ i)⁻¹ ∈ H.carrier
    simp only [Nat.pred_succ, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
      Subgroup.mem_toSubmonoid, inv_mem_iff, imp_self]
  . intro i j h1 h2
    change QuotientGroup.mk _ ∈ H.carrier
    rw [QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ h1 h2

theorem braid_group_2.is_cyclic : ∃ g : (braid_group 2), ∀ x, x ∈ Subgroup.zpowers g := by
  use (σ 0)
  intro x
  apply generated_by
  intro i
  rw [Subgroup.mem_zpowers_iff]
  have h : i=0 := by
    apply Fin.eq_of_val_eq
    simp
  use 1
  rw [h]
  rfl

theorem embed_helper (n : ℕ) : ∀ (a b : FreeMonoid' (Fin (n.pred))),
    (braid_rels_m (n.pred)) a b → ((FreeMonoid'.lift fun a => σ a) a : braid_group n)=
    (FreeMonoid'.lift fun a => σ a) b := by
  repeat
    rcases n
    · intro _ _ h
      exfalso
      apply h
    rename_i n
  intro a b h
  rcases h
  · rename_i j
    simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
    apply braid_group.braid
  simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
  apply braid_group.comm
  next ih => exact ih

/--
Relation-respecting monoid hom from the presented positive braid monoid to the
presented braid group.

Despite the historical name, this declaration does not prove injectivity.
-/
def embed {n : ℕ} : (BraidMonoid n) →* (braid_group (n)) :=
  PresentedMonoid.toMonoid (fun a => @σ (n.pred) a) (embed_helper n)

theorem embed_inf_helper : ∀ (a b : FreeMonoid' ℕ),
    (braid_rels_m_inf a b → ((FreeMonoid'.lift fun a => σi a) a : braid_group_inf)=
    (FreeMonoid'.lift fun a => σi a) b) := by
  intro a b h
  rcases h
  · rename_i j
    simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
    apply braid_group_inf.braid
  simp only [Nat.succ_eq_add_one, map_mul, FreeMonoid'.lift_eval_of, Nat.pred_succ]
  apply braid_group_inf.comm
  next ih => exact ih

/--
Relation-respecting monoid hom from the infinite positive braid monoid to the
presented infinite braid group.

Despite the historical name, this declaration does not prove injectivity and
does not instantiate the Ore-localization equivalence for `BraidMonoidInf`.
-/
def embed_inf : BraidMonoidInf →* braid_group_inf :=
  PresentedMonoid.toMonoid (fun a => σi a) embed_inf_helper

/-! ## Universal target-group maps for the presented braid groups -/

/--
Universal map out of the finite braid group `B_{n+1}`.

This is the promised thin repackaging of `PresentedGroup.toGroup`: to define a
homomorphism out of the braid group it is enough to give the images of the `n`
Artin generators and prove that every relation in the already-owned
`braid_rels n` is sent to the identity.
-/
noncomputable def braid_group.toGroup
    {n : ℕ} {G : Type*} [Group G]
    (f : Fin n → G)
    (hrels : ∀ r ∈ braid_rels n, FreeGroup.lift f r = 1) :
    braid_group (n + 1) →* G := by
  change PresentedGroup (braid_rels n) →* G
  exact PresentedGroup.toGroup (f := f) hrels

@[simp]
theorem braid_group.toGroup_sigma
    {n : ℕ} {G : Type*} [Group G]
    (f : Fin n → G)
    (hrels : ∀ r ∈ braid_rels n, FreeGroup.lift f r = 1)
    (i : Fin n) :
    braid_group.toGroup f hrels (σ' n i) = f i := by
  exact PresentedGroup.toGroup.of hrels

/-- A homomorphism out of `B_{n+1}` is uniquely determined by its Artin
generator images. -/
theorem braid_group.toGroup_unique
    {n : ℕ} {G : Type*} [Group G]
    (f : Fin n → G)
    (hrels : ∀ r ∈ braid_rels n, FreeGroup.lift f r = 1)
    (φ : braid_group (n + 1) →* G)
    (hφ : ∀ i : Fin n, φ (σ' n i) = f i) :
    φ = braid_group.toGroup f hrels := by
  apply PresentedGroup.ext
  intro i
  exact (hφ i).trans (braid_group.toGroup_sigma f hrels i).symm

/-- Universal map out of the infinite braid group `B_∞`. -/
noncomputable def braid_group_inf.toGroup
    {G : Type*} [Group G]
    (f : ℕ → G)
    (hrels : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1) :
    braid_group_inf →* G :=
  PresentedGroup.toGroup (f := f) hrels

@[simp]
theorem braid_group_inf.toGroup_sigma
    {G : Type*} [Group G]
    (f : ℕ → G)
    (hrels : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1)
    (i : ℕ) :
    braid_group_inf.toGroup f hrels (σi i) = f i := by
  exact PresentedGroup.toGroup.of hrels

/-- A homomorphism out of `B_∞` is uniquely determined by its countable Artin
generator images. -/
theorem braid_group_inf.toGroup_unique
    {G : Type*} [Group G]
    (f : ℕ → G)
    (hrels : ∀ r ∈ braid_rels_inf, FreeGroup.lift f r = 1)
    (φ : braid_group_inf →* G)
    (hφ : ∀ i : ℕ, φ (σi i) = f i) :
    φ = braid_group_inf.toGroup f hrels := by
  apply PresentedGroup.ext
  intro i
  exact (hφ i).trans (braid_group_inf.toGroup_sigma f hrels i).symm

/-! ## Artin-law data for finite braid-group targets -/

/--
Generator images satisfying exactly the local laws of the finite braid
presentation.

The adjacent law is stated for any pair of consecutive indices, while the far
law is stated for indices separated by at least two.  This keeps downstream
tensor-power constructions independent of the internal relation-set syntax.
-/
structure braid_group.HomData (n : ℕ) (G : Type*) [Group G] where
  generator : Fin n → G
  adjacent :
    ∀ (i j : Fin n), j.val = i.val + 1 →
      generator i * generator j * generator i =
        generator j * generator i * generator j
  far_commute :
    ∀ (i j : Fin n), i.val + 2 ≤ j.val →
      generator i * generator j = generator j * generator i

namespace braid_group.HomData

/-- The local Artin and far-commutation laws kill every word in the repository's
owned relation set. -/
theorem relations
    {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G) :
    ∀ r ∈ braid_rels n, FreeGroup.lift d.generator r = 1 := by
  intro r hr
  cases n with
  | zero =>
      simp [braid_rels] at hr
  | succ n =>
      cases n with
      | zero =>
          simp [braid_rels] at hr
      | succ n =>
          have hrels :
              (∃ i : Fin (n + 1),
                  r = braid_rel (i.castSucc) (i.succ)) ∨
                (∃ i j : Fin n, i ≤ j ∧
                  r = comm_rel (i.castSucc.castSucc) (j.succ.succ)) := by
            simpa only [braid_rels, Set.mem_union, Set.mem_setOf_eq] using hr
          rcases hrels with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
          · have hArtin :=
              d.adjacent i.castSucc i.succ (by rfl)
            simp only [braid_rel, map_mul, map_inv,
              FreeGroup.lift_apply_of]
            rw [hArtin]
            simp [mul_assoc]
          · have hsep :
                (i.castSucc.castSucc : Fin (n + 2)).val + 2 ≤
                  (j.succ.succ : Fin (n + 2)).val := by
              simpa using Nat.add_le_add_right hij 2
            have hcomm :=
              d.far_commute i.castSucc.castSucc j.succ.succ hsep
            simp only [comm_rel, map_mul, map_inv,
              FreeGroup.lift_apply_of]
            rw [hcomm]
            simp [mul_assoc]

/-- Universal finite braid-group homomorphism generated by local Artin data. -/
noncomputable def toGroupHom
    {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G) :
    braid_group (n + 1) →* G :=
  braid_group.toGroup d.generator d.relations

@[simp]
theorem toGroupHom_sigma
    {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G) (i : Fin n) :
    d.toGroupHom (σ' n i) = d.generator i :=
  braid_group.toGroup_sigma d.generator d.relations i

/-- The locally generated homomorphism is unique with its prescribed generator
images. -/
theorem toGroupHom_unique
    {n : ℕ} {G : Type*} [Group G]
    (d : braid_group.HomData n G)
    (φ : braid_group (n + 1) →* G)
    (hφ : ∀ i : Fin n, φ (σ' n i) = d.generator i) :
    φ = d.toGroupHom :=
  braid_group.toGroup_unique d.generator d.relations φ hφ

end braid_group.HomData

end Braid
