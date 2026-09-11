import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

/-!
Theorem 5 archive surface: Fibonacci braid-space dimensions and a representation
schema.

The `BraidGroup` structure below is a record of a matrix family together with
proof fields for the Artin relations.  The file does not instantiate such a
family with concrete Fibonacci matrices.
-/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

def conformalBlockDim (n : ℕ) : ℕ :=
  if 1 ≤ n then fib (n - 1) else 0

example : conformalBlockDim 4 = 2 := rfl
example : conformalBlockDim 5 = 3 := rfl
example : conformalBlockDim 6 = 5 := rfl
example : conformalBlockDim 7 = 8 := rfl
example : conformalBlockDim 8 = 13 := rfl

/-- Schema for a candidate matrix representation satisfying Artin relations. -/
structure BraidGroup (n : ℕ) where
  generators : Fin (n-1) → Matrix (Fin (fib (n-1))) (Fin (fib (n-1))) ℂ
  rel1 : ∀ (i : ℕ) (hi : i < n - 2),
    have hi1 : i < n - 1 := by omega
    have hi2 : i + 1 < n - 1 := by omega
    generators ⟨i, hi1⟩ * generators ⟨i + 1, hi2⟩ * generators ⟨i, hi1⟩ =
    generators ⟨i + 1, hi2⟩ * generators ⟨i, hi1⟩ * generators ⟨i + 1, hi2⟩
  rel2 : ∀ (i j : ℕ) (hi : i < n - 1) (hj : j < n - 1),
    i + 1 < j → generators ⟨i, hi⟩ * generators ⟨j, hj⟩ = generators ⟨j, hj⟩ * generators ⟨i, hi⟩

end
