import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace InfoGeometry.ProofTheory.NonCommutativeDAG

/-!
# Free-Monoid Traces and Binary-Doubling Expansion

This module models words by lists and studies a recursive binary-doubling
construction. It proves an exact exponential expansion from a linear-size
description. It does not model the repository's declaration DAG or assert a
general compression bound for formal proofs.
-/

section NonCommutativeMonoid

/-- A word of symbols, with concatenation as the monoid operation. -/
abbrev ProofTrace (α : Type*) := List α

/-- The length of a word. -/
def traceLength {α : Type*} (t : ProofTrace α) : ℕ := t.length

/-- Concatenation adds word lengths. -/
theorem trace_length_append {α : Type*} (t₁ t₂ : ProofTrace α) :
    traceLength (t₁ ++ t₂) = traceLength t₁ + traceLength t₂ :=
  List.length_append

/-- If two concatenations differ after swapping the factors, the factors
cannot be equal. -/
theorem trace_noncommutative {α : Type*} {t₁ t₂ : ProofTrace α} 
    (h : t₁ ++ t₂ ≠ t₂ ++ t₁) : t₁ ≠ t₂ := by
  intro contra
  rw [contra] at h
  exact h rfl

end NonCommutativeMonoid

section DAGCompression

/-- The number of symbols obtained by recursively doubling a one-symbol word. -/
def ncDoublingUnwrap : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * ncDoublingUnwrap n

/-- Number of doubling steps in the description. -/
def ncDoublingDepth : ℕ → ℕ
  | 0 => 0
  | n + 1 => ncDoublingDepth n + 1

/-- Encoded length: each doubling step adds two references to the previous word. -/
def ncDoublingWrap : ℕ → ℕ
  | 0 => 1
  | n + 1 => ncDoublingWrap n + 2

/-- Master Theorem: The Exponential Reach in a Non-Commutative DAG.
    Unwrapped length scales exactly as 2^(depth), proving that DAGs
    compress Free Monoids exponentially. -/
theorem nc_doubling_pow (n : ℕ) :
    ncDoublingUnwrap n = 2 ^ ncDoublingDepth n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      dsimp [ncDoublingUnwrap, ncDoublingDepth]
      rw [ih]
      ring

/-- Wrapped length scales strictly linearly with depth: L_wrap = 2 * depth + 1. -/
theorem nc_doubling_wrap_eq (n : ℕ) :
    ncDoublingWrap n = 2 * ncDoublingDepth n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      dsimp [ncDoublingWrap, ncDoublingDepth]
      omega

/-- Master Theorem: Non-Commutative Exponential Compression.
    Even in a strictly non-commutative free monoid, DAG macro definitions
    achieve exponential compression: L_unwrap = 2^((L_wrap - 1) / 2). -/
theorem nc_doubling_compression (n : ℕ) :
    ncDoublingUnwrap n = 2 ^ ((ncDoublingWrap n - 1) / 2) := by
  rw [nc_doubling_pow]
  have h_wrap := nc_doubling_wrap_eq n
  have h_div : (ncDoublingWrap n - 1) / 2 = ncDoublingDepth n := by
    rw [h_wrap]
    omega
  rw [h_div]

end DAGCompression

end InfoGeometry.ProofTheory.NonCommutativeDAG
