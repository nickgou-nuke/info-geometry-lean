import Mathlib

/-!
# Exact signed-ensemble cancellation, independently of sheet or orientation

A cell includes every label needed to evaluate an observable, including a
sheet label when sheets are observable. Neither the sample sign nor its
negative is identified with chirality, a commutant, or reversal of an edge.

No multiplication on the payload is used: these results also apply to the
additive carrier of nonassociative operator-Zorn fields.
-/

namespace InfoGeometry.SignedNetwork.ExactCancellation

@[ext] structure Counts (C : Type*) where
  positive : C → ℕ
  negative : C → ℕ

variable {C : Type*}

def signed (p : Counts C) : C → ℤ :=
  fun c => (p.positive c : ℤ) - (p.negative c : ℤ)

def annihilationCount (p : Counts C) (c : C) : ℕ :=
  min (p.positive c) (p.negative c)

def cancel (p : Counts C) : Counts C :=
  ⟨fun c => p.positive c - p.negative c,
   fun c => p.negative c - p.positive c⟩

/-- Addition of zero signed mass, cell by cell. -/
def addNullPairs (p : Counts C) (k : C → ℕ) : Counts C :=
  ⟨fun c => p.positive c + k c, fun c => p.negative c + k c⟩

@[simp] theorem signed_cancel (p : Counts C) : signed (cancel p) = signed p := by
  funext c
  dsimp [signed, cancel]
  omega

@[simp] theorem signed_addNullPairs (p : Counts C) (k : C → ℕ) :
    signed (addNullPairs p k) = signed p := by
  funext c
  dsimp [signed, addNullPairs]
  omega

theorem cancel_positive_eq_remove_pairs (p : Counts C) (c : C) :
    (cancel p).positive c = p.positive c - annihilationCount p c := by
  dsimp [cancel, annihilationCount]
  omega

theorem cancel_negative_eq_remove_pairs (p : Counts C) (c : C) :
    (cancel p).negative c = p.negative c - annihilationCount p c := by
  dsimp [cancel, annihilationCount]
  omega

theorem cancel_one_sign (p : Counts C) (c : C) :
    (cancel p).positive c = 0 ∨ (cancel p).negative c = 0 := by
  dsimp [cancel]
  omega

@[simp] theorem cancel_idempotent (p : Counts C) : cancel (cancel p) = cancel p := by
  apply Counts.ext <;> funext c <;> dsimp [cancel] <;> omega

/-- A sample-count statistic is not a statistic of the signed state. -/
theorem annihilationCount_addNullPairs (p : Counts C) (k : C → ℕ) (c : C) :
    annihilationCount (addNullPairs p k) c = annihilationCount p c + k c := by
  dsimp [annihilationCount, addNullPairs]
  omega

/-- No state-only functional can recover the number of cancelled pairs. -/
theorem no_annihilationCount_function_of_signed (c : C) :
    ¬ ∃ F : (C → ℤ) → ℕ, ∀ p : Counts C,
      F (signed p) = annihilationCount p c := by
  rintro ⟨F, hF⟩
  have h0 := hF (Counts.mk (fun _ => 0) (fun _ => 0))
  have h1 := hF (Counts.mk (fun _ => 1) (fun _ => 1))
  norm_num [signed, annihilationCount] at h0 h1
  omega

section Readout

variable [Fintype C] {A : Type*} [AddCommGroup A]

/-- An unnormalized signed observable, not automatically a probability. -/
def readout (p : Counts C) (O : C → A) : A :=
  ∑ c, signed p c • O c

@[simp] theorem readout_cancel (p : Counts C) (O : C → A) :
    readout (cancel p) O = readout p O := by
  simp only [readout, signed_cancel]

@[simp] theorem readout_addNullPairs (p : Counts C) (k : C → ℕ) (O : C → A) :
    readout (addNullPairs p k) O = readout p O := by
  simp only [readout, signed_addNullPairs]

end Readout

/-- If the two signs use different transports, a null pair need not stay null.
Cancellation of every null pair is equivalent to equality of the transports. -/
theorem all_null_pairs_preserved_iff
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (forward backward : A →+ B) :
    (∀ x, forward x - backward x = 0) ↔ forward = backward := by
  constructor
  · intro h
    ext x
    exact sub_eq_zero.mp (h x)
  · rintro rfl x
    exact sub_self _

/-- Cancellation after any common additive transport is exact. -/
theorem common_transport_cancels
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (T : A →+ B) (x : A) : T x + T (-x) = 0 := by
  simp

end InfoGeometry.SignedNetwork.ExactCancellation
