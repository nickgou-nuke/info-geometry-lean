/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder

/-!
# The causal order of ranked dependencies

The order is reachability in the supplied dependency relation. A natural-number
rank certifies that each actual dependency precedes its consumer; it is used
only to establish antisymmetry. Dependency-closed sets are precisely the lower
sets of this order. No global order instance is installed on the key type.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork.Dependency

variable {κ : Type*}

/-- A key precedes a consumer if a finite chain of actual dependencies connects them. -/
def Reachable (deps : κ → Set κ) : κ → κ → Prop :=
  Relation.ReflTransGen (fun d k => d ∈ deps k)

@[refl] theorem reachable_refl (deps : κ → Set κ) (k : κ) : Reachable deps k k :=
  Relation.ReflTransGen.refl

theorem dependency_reachable {deps : κ → Set κ} {d k : κ} (h : d ∈ deps k) :
    Reachable deps d k :=
  Relation.ReflTransGen.single h

@[trans] theorem reachable_trans {deps : κ → Set κ} {d k l : κ}
    (hdk : Reachable deps d k) (hkl : Reachable deps k l) : Reachable deps d l :=
  Relation.ReflTransGen.trans hdk hkl

section Ranked

variable {deps : κ → Set κ} (rank : κ → ℕ)
  (hrank : ∀ ⦃d k : κ⦄, d ∈ deps k → rank d < rank k)

include hrank

theorem rank_mono {d k : κ} (h : Reachable deps d k) : rank d ≤ rank k := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact le_trans ih (le_of_lt (hrank h))

theorem eq_or_rank_lt {d k : κ} (h : Reachable deps d k) :
    d = k ∨ rank d < rank k := by
  cases h with
  | refl => exact Or.inl rfl
  | tail h e => exact Or.inr (lt_of_le_of_lt (rank_mono rank hrank h) (hrank e))

theorem rank_strict_of_ne {d k : κ} (h : Reachable deps d k) (hne : d ≠ k) :
    rank d < rank k := by
  rcases eq_or_rank_lt rank hrank h with heq | hlt
  · exact False.elim (hne heq)
  · exact hlt

theorem reachable_eq_of_rank_eq {d k : κ} (h : Reachable deps d k)
    (heq : rank d = rank k) : d = k := by
  rcases eq_or_rank_lt rank hrank h with hdk | hlt
  · exact hdk
  · rw [heq] at hlt
    exact False.elim ((lt_irrefl _) hlt)

theorem reachable_antisymm {d k : κ}
    (hdk : Reachable deps d k) (hkd : Reachable deps k d) : d = k := by
  rcases eq_or_rank_lt rank hrank hdk with h | h
  · exact h
  · exact False.elim ((not_lt_of_ge (rank_mono rank hrank hkd)) h)

theorem dependency_no_reverse {d k : κ} (h : d ∈ deps k) : ¬ Reachable deps k d := by
  intro hkd
  exact (not_lt_of_ge (rank_mono rank hrank hkd)) (hrank h)

/-- The native partial order determined by actual dependency reachability. -/
@[instance_reducible]
def dependencyOrder : PartialOrder κ where
  le := Reachable deps
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ := reachable_antisymm rank hrank

theorem dependencyOrder_le_iff (d k : κ) :
    @LE.le κ (dependencyOrder rank hrank).toLE d k ↔ Reachable deps d k := Iff.rfl

theorem dependencyOrder_edge_lt {d k : κ} (h : d ∈ deps k) :
    @LT.lt κ (dependencyOrder rank hrank).toLT d k := by
  change Reachable deps d k ∧ ¬ Reachable deps k d
  exact ⟨dependency_reachable h, dependency_no_reverse rank hrank h⟩

end Ranked

/-- Every immediate dependency of a retained key is also retained. -/
def Closed (deps : κ → Set κ) (S : Set κ) : Prop :=
  ∀ ⦃d k : κ⦄, k ∈ S → d ∈ deps k → d ∈ S

/-- Immediate closure already supplies every finite transitive dependency. -/
theorem closed_under_reachable {deps : κ → Set κ} {S : Set κ} (hS : Closed deps S)
    {d k : κ} (h : Reachable deps d k) : k ∈ S → d ∈ S := by
  induction h with
  | refl => exact id
  | tail _ h ih =>
    intro hk
    exact ih (hS hk h)

theorem closed_iff_reachable_closed (deps : κ → Set κ) (S : Set κ) :
    Closed deps S ↔
      ∀ ⦃d k : κ⦄, Reachable deps d k → k ∈ S → d ∈ S := by
  constructor
  · intro hS d k hdk
    exact closed_under_reachable hS hdk
  · intro h d k hk hd
    exact h (dependency_reachable hd) hk

/-- The same closure condition is native lower-set closure for the derived causal order. -/
theorem closed_iff_isLowerSet (deps : κ → Set κ) (rank : κ → ℕ)
    (hrank : ∀ ⦃d k : κ⦄, d ∈ deps k → rank d < rank k) (S : Set κ) :
    Closed deps S ↔ @IsLowerSet κ (dependencyOrder rank hrank).toLE S := by
  constructor
  · intro hS a b hab hb
    exact closed_under_reachable hS hab hb
  · intro h d k hk hd
    exact h (dependency_reachable hd) hk

end InfoGeometry.Canonical.OperatorContentNetwork.Dependency
