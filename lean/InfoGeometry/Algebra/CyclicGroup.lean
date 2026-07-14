import Mathlib.GroupTheory.SpecificGroups.Cyclic

open Subgroup

universe u

namespace CyclicGroup

section GroupDefinition

variable (G : Type u) [Group G]

/-- Explicit cyclicity: every element is an integer power of a generator. -/
def IsCyclicExplicit : Prop :=
  ∃ g : G, ∀ x : G, ∃ n : ℤ, g ^ n = x

/-- For a fixed generator, the explicit integer-power formulation is equivalent
to the subgroup-closure formulation. -/
theorem cyclic_explicit_iff_closure (g : G) :
    (∀ x : G, ∃ n : ℤ, g ^ n = x) ↔ Subgroup.closure ({g} : Set G) = ⊤ := by
  constructor
  · intro h
    rw [← Subgroup.zpowers_eq_closure]
    apply (Subgroup.eq_top_iff' (Subgroup.zpowers g)).2
    intro x
    rcases h x with ⟨n, rfl⟩
    exact Subgroup.zpow_mem_zpowers g n
  · intro h x
    have hx : x ∈ Subgroup.closure ({g} : Set G) := by
      rw [h]
      simp
    rcases Subgroup.mem_closure_singleton.mp hx with ⟨n, hn⟩
    exact ⟨n, hn⟩

/-- The explicit and mathlib cyclicity formulations are equivalent. -/
theorem cyclic_explicit_iff :
    IsCyclicExplicit G ↔ IsCyclic G := by
  constructor
  · rintro ⟨g, hg⟩
    refine (isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ?_
    refine ⟨g, ?_⟩
    rw [Subgroup.zpowers_eq_closure]
    exact (cyclic_explicit_iff_closure G g).1 hg
  · intro h
    rcases (isCyclic_iff_exists_zpowers_eq_top (α := G)).1 h with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    exact (cyclic_explicit_iff_closure G g).2 (by
      rw [Subgroup.zpowers_eq_closure] at hg
      exact hg)

end GroupDefinition

noncomputable section

section Classification

/-!
#### BUCKET 1: CLOSED OWNER THEOREMS
Exact owner theorems proved from real definitions, Mathlib, and existing owner lemmas.
-/

/-- Every infinite cyclic group is isomorphic to `Multiplicative ℤ`. -/
noncomputable def infinite_cyclic_iso_int {G : Type u} [Group G] [Infinite G] [IsCyclic G] :
    G ≃* Multiplicative ℤ := by
  classical
  have hcard : Nat.card G = Nat.card (Multiplicative ℤ) := by
    rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite]
  exact mulEquivOfCyclicCardEq (G := G) (G' := Multiplicative ℤ) hcard

/-- Every finite cyclic group of order `Nat.card G` is isomorphic to
`Multiplicative (ZMod (Nat.card G))`. -/
noncomputable def finite_cyclic_iso_zmod {G : Type u} [Group G] [Finite G] [IsCyclic G] :
    G ≃* Multiplicative (ZMod (Nat.card G)) :=
  (zmodCyclicMulEquiv (G := G) (h := inferInstance)).symm

/-- Every subgroup of a cyclic group is cyclic. -/
theorem subgroup_of_cyclic_is_cyclic {G : Type u} [Group G] [IsCyclic G] (H : Subgroup G) :
    IsCyclic H := by
  infer_instance

end Classification

end
