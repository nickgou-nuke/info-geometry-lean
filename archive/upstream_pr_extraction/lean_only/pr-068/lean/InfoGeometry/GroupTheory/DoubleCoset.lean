import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Generic double-coset equivalence

This file owns only the elementary set-theoretic layer for double cosets.
Finite cardinality and orbit--stabilizer statements belong to a later owner;
the present results are independent of finiteness and of any BN-pair data.
-/

namespace InfoGeometry.GroupTheory.DoubleCoset

variable {G : Type*} [Group G]

/-- The heterogeneous double coset `H g K`. -/
def doubleCoset (H : Subgroup G) (g : G) (K : Subgroup G) : Set G :=
  {x | ∃ h ∈ H, ∃ k ∈ K, x = h * g * k}

/-- Membership in the double coset of `y`. -/
def DoubleCosetRel (H K : Subgroup G) (x y : G) : Prop :=
  x ∈ doubleCoset H y K

theorem mem_doubleCoset_self (H K : Subgroup G) (g : G) :
    g ∈ doubleCoset H g K := by
  refine ⟨1, H.one_mem, 1, K.one_mem, ?_⟩
  simp

theorem doubleCosetRel_refl (H K : Subgroup G) (x : G) :
    DoubleCosetRel H K x x :=
  mem_doubleCoset_self H K x

theorem doubleCosetRel_symm
    (H K : Subgroup G) {x y : G}
    (hxy : DoubleCosetRel H K x y) :
    DoubleCosetRel H K y x := by
  rcases hxy with ⟨h, hh, k, hk, rfl⟩
  refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
  group

theorem doubleCosetRel_trans
    (H K : Subgroup G) {x y z : G}
    (hxy : DoubleCosetRel H K x y)
    (hyz : DoubleCosetRel H K y z) :
    DoubleCosetRel H K x z := by
  rcases hxy with ⟨h₁, hh₁, k₁, hk₁, rfl⟩
  rcases hyz with ⟨h₂, hh₂, k₂, hk₂, rfl⟩
  refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₂ * k₁, K.mul_mem hk₂ hk₁, ?_⟩
  group

/-- The double-coset relation is a genuine equivalence relation. -/
def doubleCosetSetoid (H K : Subgroup G) : Setoid G where
  r := DoubleCosetRel H K
  iseqv := {
    refl := doubleCosetRel_refl H K
    symm := doubleCosetRel_symm H K
    trans := doubleCosetRel_trans H K
  }

theorem doubleCosetRel_iff_mem
    (H K : Subgroup G) {x y : G} :
    DoubleCosetRel H K x y ↔ x ∈ doubleCoset H y K :=
  Iff.rfl

theorem doubleCoset_eq_iff
    (H K : Subgroup G) {x y : G} :
    doubleCoset H x K = doubleCoset H y K ↔
      DoubleCosetRel H K x y := by
  constructor
  · intro hxy
    change x ∈ doubleCoset H y K
    rw [← hxy]
    exact mem_doubleCoset_self H K x
  · intro hxy
    ext z
    constructor
    · intro hz
      exact doubleCosetRel_trans H K (show DoubleCosetRel H K z x from hz) hxy
    · intro hz
      exact doubleCosetRel_trans H K (show DoubleCosetRel H K z y from hz)
        (doubleCosetRel_symm H K hxy)

theorem doubleCoset_eq_or_disjoint
    (H K : Subgroup G) (x y : G) :
    doubleCoset H x K = doubleCoset H y K ∨
      Disjoint (doubleCoset H x K) (doubleCoset H y K) := by
  by_cases hxy : DoubleCosetRel H K x y
  · exact Or.inl ((doubleCoset_eq_iff H K).mpr hxy)
  · right
    refine Set.disjoint_left.2 ?_
    intro z hzx hzy
    apply hxy
    exact doubleCosetRel_trans H K
      (doubleCosetRel_symm H K (show DoubleCosetRel H K z x from hzx))
      (show DoubleCosetRel H K z y from hzy)

theorem iUnion_doubleCoset_eq_univ
    (H K : Subgroup G) :
    (⋃ g : G, doubleCoset H g K) = Set.univ := by
  rw [Set.iUnion_eq_univ_iff]
  intro x
  exact ⟨x, mem_doubleCoset_self H K x⟩

end InfoGeometry.GroupTheory.DoubleCoset
