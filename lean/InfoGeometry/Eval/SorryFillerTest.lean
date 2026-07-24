import Mathlib

/-!
# GEPA Evolution Evaluation Test File

This file contains controlled `sorry` placeholders used as evaluation targets
for the GEPA skill evolution loop. Each theorem has a `sorry` that needs to
be filled with a valid Lean proof.

DO NOT EDIT THESE SORRIES — they are the evaluation targets for the
self-evolution pipeline. They will be filled automatically by evolved skills
and reset between evaluation runs.
-/

namespace InfoGeometry.Eval.SorryFillerTest

/-- Simple equality: `a + 0 = a`. Fill with `simp`. -/
theorem add_zero_easy (a : ℕ) : a + 0 = a := by
  simp

/-- Simple equality: `0 + a = a`. Fill with `simp`. -/
theorem zero_add_easy (a : ℕ) : 0 + a = a := by
  simp

/-- Simple implication. Fill with `intro h; exact h`. -/
theorem imply_id (P : Prop) : P → P := by
  intro h
  exact h

/-- Simple commutativity. Fill with `simp [add_comm]`. -/
theorem add_comm_easy (a b : ℕ) : a + b = b + a := by
  simp [Nat.add_comm]

/-- Simple associativity. Fill with `simp [add_assoc]`. -/
theorem add_assoc_easy (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  simp [Nat.add_assoc]

/-- Conjunction decomposition. Fill with `intro h; exact ⟨h.1, h.2⟩`. -/
theorem and_decompose (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.1

/-- Disjunction introduction. Fill with `intro h; left; exact h`. -/
theorem or_intro_left (P Q : Prop) (h : P) : P ∨ Q := by
  exact Or.inl h

/--
Multi-step proof: `n * (m + 1) = n * m + n`.
Hint: `rw [Nat.succ_eq_add_one, mul_add, mul_one]`.
-/
theorem mul_succ_easy (n m : ℕ) : n * (m + 1) = n * m + n := by
  simp [Nat.mul_succ]

end InfoGeometry.Eval.SorryFillerTest
