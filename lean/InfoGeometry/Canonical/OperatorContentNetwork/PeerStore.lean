/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.Basic

/-!
# Compatible exchange of partial operator-program stores

Extension retains every existing entry. The left-biased merge is associative
and idempotent; its two orders agree exactly when overlapping payloads agree.
Compatible merge is the least common extension in the native partial order.
These are laws of exchanging program data, not laws of matrix multiplication.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork.PeerStore

abbrev Store (κ α : Type*) := κ → Option (Program α)

variable {κ α : Type*}

def Compatible (S T : Store κ α) : Prop :=
  ∀ k p q, S k = some p → T k = some q → p = q

def Extends (S T : Store κ α) : Prop :=
  ∀ k p, S k = some p → T k = some p

def merge (S T : Store κ α) : Store κ α :=
  fun k => match S k with
    | some p => some p
    | none => T k

def domain (S : Store κ α) : Set κ := {k | ∃ p, S k = some p}

theorem compatible_refl (S : Store κ α) : Compatible S S := by
  intro k p q hp hq
  exact Option.some.inj (hp.symm.trans hq)

theorem compatible_symm {S T : Store κ α} (h : Compatible S T) : Compatible T S :=
  fun k p q hp hq => (h k q p hq hp).symm

theorem extends_refl (S : Store κ α) : Extends S S := fun _ _ h => h

theorem extends_trans {S T U : Store κ α} (hST : Extends S T) (hTU : Extends T U) :
    Extends S U := fun k p h => hTU k p (hST k p h)

theorem extends_antisymm {S T : Store κ α} (hST : Extends S T) (hTS : Extends T S) :
    S = T := by
  funext k
  cases hS : S k with
  | none =>
    cases hT : T k with
    | none => rfl
    | some p =>
      have h := hTS k p hT
      simp [hS] at h
  | some p => exact (hST k p hS).symm

/-- The native order whose comparison means retention of all stored entries. -/
@[instance_reducible] def extensionOrder : PartialOrder (Store κ α) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm _ _ := extends_antisymm

@[simp] theorem merge_of_some (S T : Store κ α) {k : κ} {p : Program α}
    (h : S k = some p) : merge S T k = some p := by
  simp [merge, h]

theorem merge_of_none (S T : Store κ α) {k : κ} (h : S k = none) :
    merge S T k = T k := by
  simp [merge, h]

theorem merge_eq_some_iff (S T : Store κ α) (k : κ) (p : Program α) :
    merge S T k = some p ↔ S k = some p ∨ (S k = none ∧ T k = some p) := by
  cases hS : S k <;> simp [merge, hS]

theorem merge_assoc (S T U : Store κ α) : merge (merge S T) U = merge S (merge T U) := by
  funext k
  cases hS : S k <;> simp [merge, hS]

@[simp] theorem merge_idem (S : Store κ α) : merge S S = S := by
  funext k
  cases hS : S k <;> simp [merge, hS]

/-- Equality of the two exchange orders is equivalent to overlap agreement. -/
theorem merge_comm_iff (S T : Store κ α) : merge S T = merge T S ↔ Compatible S T := by
  constructor
  · intro h k p q hS hT
    have hk := congrFun h k
    simpa [merge, hS, hT] using hk
  · intro h
    funext k
    cases hS : S k with
    | none => cases hT : T k <;> simp [merge, hS, hT]
    | some p =>
      cases hT : T k with
      | none => simp [merge, hS, hT]
      | some q => simp [merge, hS, hT, h k p q hS hT]

theorem extends_merge_left (S T : Store κ α) : Extends S (merge S T) :=
  fun _ _ h => merge_of_some S T h

theorem extends_merge_right {S T : Store κ α} (h : Compatible S T) :
    Extends T (merge S T) := by
  intro k q hT
  cases hS : S k with
  | none => simp [merge, hS, hT]
  | some p => simp [merge, hS, h k p q hS hT]

theorem merge_least {S T U : Store κ α} (hS : Extends S U) (hT : Extends T U) :
    Extends (merge S T) U := by
  intro k p hp
  rcases (merge_eq_some_iff S T k p).1 hp with hs | ⟨_, ht⟩
  · exact hS k p hs
  · exact hT k p ht

theorem compatible_of_common_extension {S T U : Store κ α}
    (hS : Extends S U) (hT : Extends T U) : Compatible S T := by
  intro k p q hp hq
  exact Option.some.inj ((hS k p hp).symm.trans (hT k q hq))

/-- A common extension exists precisely when the stores can be exchanged without conflict. -/
theorem compatible_iff_common_extension (S T : Store κ α) :
    Compatible S T ↔ ∃ U, Extends S U ∧ Extends T U := by
  constructor
  · intro h
    exact ⟨merge S T, extends_merge_left S T, extends_merge_right h⟩
  · rintro ⟨U, hS, hT⟩
    exact compatible_of_common_extension hS hT

theorem domain_mono {S T : Store κ α} (h : Extends S T) : domain S ⊆ domain T := by
  rintro k ⟨p, hp⟩
  exact ⟨p, h k p hp⟩

theorem domain_merge (S T : Store κ α) : domain (merge S T) = domain S ∪ domain T := by
  ext k
  constructor
  · rintro ⟨p, hp⟩
    rcases (merge_eq_some_iff S T k p).1 hp with hs | ⟨_, ht⟩
    · exact Or.inl ⟨p, hs⟩
    · exact Or.inr ⟨p, ht⟩
  · intro hk
    cases hS : S k with
    | some p => exact ⟨p, merge_of_some S T hS⟩
    | none =>
      rcases hk with ⟨p, hp⟩ | ⟨p, hp⟩
      · simp [hS] at hp
      · exact ⟨p, by simp [merge, hS, hp]⟩

def DependencyClosed (deps : κ → Set κ) (S : Store κ α) : Prop :=
  ∀ k ∈ domain S, deps k ⊆ domain S

/-- Exchanging two dependency-closed stores preserves closure of their common domain. -/
theorem dependencyClosed_merge {deps : κ → Set κ} {S T : Store κ α}
    (hS : DependencyClosed deps S) (hT : DependencyClosed deps T) :
    DependencyClosed deps (merge S T) := by
  intro k hk d hd
  rw [domain_merge] at hk ⊢
  rcases hk with hk | hk
  · exact Or.inl (hS k hk hd)
  · exact Or.inr (hT k hk hd)

end InfoGeometry.Canonical.OperatorContentNetwork.PeerStore
