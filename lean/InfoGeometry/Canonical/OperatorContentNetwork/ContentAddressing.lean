/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.PeerStore
import InfoGeometry.Canonical.OperatorContentNetwork.Programs
import Mathlib.Logic.Function.Basic

/-!
# Addressed program exchange and operator lookup

Address validity states that each resident payload is stored at its supplied
address. Collision freedom is assumed only on the union of the actual payload
sets. Compatible exchange retains operator lookups, but interpreting exchange
as matrix multiplication forces commutation and idempotence. Equal addresses
alone do not justify exchanging distinct programs: opposite merge orders can
retain different arbitrary real operator evaluations.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork.PeerStore.Addressing

variable {κ α : Type*}

/-- Programs actually resident in a partial store. -/
def payloads (S : Store κ α) : Set (Program α) :=
  {p | ∃ k, S k = some p}

/-- Each stored program is located at its declared address. -/
def Addressed (address : Program α → κ) (S : Store κ α) : Prop :=
  ∀ k p, S k = some p → address p = k

theorem payloads_mono {S T : Store κ α} (h : Extends S T) :
    payloads S ⊆ payloads T := by
  rintro p ⟨k, hp⟩
  exact ⟨k, h k p hp⟩

theorem payloads_merge_subset (S T : Store κ α) :
    payloads (merge S T) ⊆ payloads S ∪ payloads T := by
  rintro p ⟨k, hp⟩
  rcases (merge_eq_some_iff S T k p).1 hp with hs | ⟨_, ht⟩
  · exact Or.inl ⟨k, hs⟩
  · exact Or.inr ⟨k, ht⟩

/-- Compatibility prevents exchange from discarding either store's payloads. -/
theorem payloads_merge {S T : Store κ α} (h : Compatible S T) :
    payloads (merge S T) = payloads S ∪ payloads T := by
  apply Set.Subset.antisymm (payloads_merge_subset S T)
  rintro p (hp | hp)
  · exact payloads_mono (extends_merge_left S T) hp
  · exact payloads_mono (extends_merge_right h) hp

/-- Address validity survives merge even when distinct payloads collide. -/
theorem addressed_merge {address : Program α → κ} {S T : Store κ α}
    (hS : Addressed address S) (hT : Addressed address T) :
    Addressed address (merge S T) := by
  intro k p hp
  rcases (merge_eq_some_iff S T k p).1 hp with hs | ⟨_, ht⟩
  · exact hS k p hs
  · exact hT k p ht

/-- A correctly addressed partial function cannot contain two colliding payloads. -/
theorem addressed_payloads_injOn {address : Program α → κ} {S : Store κ α}
    (hS : Addressed address S) : Set.InjOn address (payloads S) := by
  rintro p ⟨k, hp⟩ q ⟨l, hq⟩ haddr
  have hkl : k = l := (hS k p hp).symm.trans (haddr.trans (hS l q hq))
  subst l
  exact Option.some.inj (hp.symm.trans hq)

/-- Collision freedom is needed only on the payloads currently being exchanged. -/
theorem compatible_of_addressed_injOn {address : Program α → κ} {S T : Store κ α}
    (hS : Addressed address S) (hT : Addressed address T)
    (hInj : Set.InjOn address (payloads S ∪ payloads T)) : Compatible S T := by
  intro k p q hp hq
  apply hInj (Or.inl ⟨k, hp⟩) (Or.inr ⟨k, hq⟩)
  exact (hS k p hp).trans (hT k q hq).symm

theorem compatible_iff_address_injOn {address : Program α → κ} {S T : Store κ α}
    (hS : Addressed address S) (hT : Addressed address T) :
    Compatible S T ↔ Set.InjOn address (payloads S ∪ payloads T) := by
  constructor
  · intro h
    rw [← payloads_merge h]
    exact addressed_payloads_injOn (addressed_merge hS hT)
  · exact compatible_of_addressed_injOn hS hT

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Lookup evaluates a resident program by the native free-algebra lift. -/
noncomputable def readOperator (ρ : α → Operator n) (S : Store κ α) (k : κ) :
    Option (Operator n) :=
  (S k).map (FreeAlgebra.lift ℝ ρ)

theorem readOperator_of_some (ρ : α → Operator n) {S : Store κ α}
    {k : κ} {p : Program α} (hp : S k = some p) :
    readOperator ρ S k = some (FreeAlgebra.lift ℝ ρ p) := by
  simp [readOperator, hp]

/-- An entry-preserving extension retains the matrix obtained at every old key. -/
theorem readOperator_retained {S T : Store κ α} (h : Extends S T)
    (ρ : α → Operator n) {k : κ} {p : Program α} (hp : S k = some p) :
    readOperator ρ S k = readOperator ρ T k := by
  simp [readOperator, hp, h k p hp]

/-- Merge selects an existing operator lookup according to the same entry policy. -/
theorem readOperator_merge (ρ : α → Operator n) (S T : Store κ α) (k : κ) :
    readOperator ρ (merge S T) k =
      match readOperator ρ S k with
      | some A => some A
      | none => readOperator ρ T k := by
  cases hs : S k <;> simp [readOperator, merge, hs]

omit [DecidableEq n] in
/-- A multiplicative interpretation of both compatible merge orders forces commutation. -/
theorem multiplicative_merge_forces_commute (E : Store κ α → Operator n)
    (S T : Store κ α) (h : Compatible S T)
    (hST : E (merge S T) = E S * E T) (hTS : E (merge T S) = E T * E S) :
    Commute (E S) (E T) := by
  change E S * E T = E T * E S
  calc
    E S * E T = E (merge S T) := hST.symm
    _ = E (merge T S) := congrArg E ((merge_comm_iff S T).2 h)
    _ = E T * E S := hTS

omit [DecidableEq n] in
/-- A multiplicative interpretation of self-merge can only produce an idempotent. -/
theorem multiplicative_merge_forces_idempotent (E : Store κ α → Operator n)
    (S : Store κ α) (h : E (merge S S) = E S * E S) : E S * E S = E S := by
  calc
    E S * E S = E (merge S S) := h.symm
    _ = E S := congrArg E (merge_idem S)

end Matrix

section Singletons

variable [DecidableEq κ]

/-- A single resident program, expressed as a native update of the empty store. -/
def singleton (k : κ) (p : Program α) : Store κ α :=
  Function.update (fun _ => none) k (some p)

theorem addressed_singleton (address : Program α → κ) (p : Program α) :
    Addressed address (singleton (address p) p) := by
  intro k q hq
  by_cases hk : k = address p
  · subst k
    have hpq : p = q := by simpa [singleton] using hq
    exact (congrArg address hpq).symm
  · simp [singleton, hk] at hq

/-- Two individually valid stores can be incompatible when their payload addresses collide. -/
theorem collision_incompatible (address : Program α → κ) (p q : Program α)
    (haddr : address p = address q) (hpq : p ≠ q) :
    ¬ Compatible (singleton (address p) p) (singleton (address q) q) := by
  intro h
  apply hpq
  exact h (address p) p q (by simp [singleton]) (by simp [singleton, haddr])

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A collision between observably distinct programs makes merge order visible to matrices. -/
theorem collision_changes_merge_read (address : Program α → κ) (p q : Program α)
    (haddr : address p = address q) (ρ : α → Operator n)
    (hEval : FreeAlgebra.lift ℝ ρ p ≠ FreeAlgebra.lift ℝ ρ q) :
    readOperator ρ (merge (singleton (address p) p) (singleton (address q) q)) (address p) ≠
      readOperator ρ (merge (singleton (address q) q) (singleton (address p) p)) (address p) := by
  simpa [readOperator, merge, singleton, haddr] using hEval

end Singletons

end InfoGeometry.Canonical.OperatorContentNetwork.PeerStore.Addressing
