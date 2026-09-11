import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Exact cancellation for finitely labelled signed counts.  The sign is an
additive coefficient; it is not identified with an orientation or a second
algebraic sheet. -/

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

theorem cancel_one_sign (p : Counts C) (c : C) :
    (cancel p).positive c = 0 ∨ (cancel p).negative c = 0 := by
  dsimp [cancel]
  omega

@[simp] theorem cancel_idempotent (p : Counts C) : cancel (cancel p) = cancel p := by
  apply Counts.ext <;> funext c <;> dsimp [cancel] <;> omega

theorem annihilationCount_addNullPairs (p : Counts C) (k : C → ℕ) (c : C) :
    annihilationCount (addNullPairs p k) c = annihilationCount p c + k c := by
  dsimp [annihilationCount, addNullPairs]
  omega

theorem no_annihilationCount_function_of_signed (c : C) :
    ¬ ∃ F : (C → ℤ) → ℕ, ∀ p : Counts C,
      F (signed p) = annihilationCount p c := by
  rintro ⟨F, hF⟩
  let p0 : Counts C := Counts.mk (fun _ => 0) (fun _ => 0)
  let p1 : Counts C := Counts.mk (fun _ => 1) (fun _ => 1)
  have h0 := hF p0
  have h1 := hF p1
  have hsame :
      signed p0 = signed p1 := by
    funext x
    simp [p0, p1, signed]
  have h0' : F (signed p0) = 0 := by
    simpa [annihilationCount] using h0
  have h1' : F (signed p1) = 1 := by
    simpa [annihilationCount] using h1
  rw [← hsame] at h1'
  omega

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

end InfoGeometry.SignedNetwork.ExactCancellation
