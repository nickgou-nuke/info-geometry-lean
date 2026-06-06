import Mathlib

noncomputable section

/-! Theorem 5: Braid Group Bn Representation -/

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

/-- The matrix family carried by a Fibonacci braid representation on `n` strands. -/
abbrev braidGeneratorFamily (n : ℕ) : Type :=
  Fin (n - 1) → Matrix (Fin (fib (n - 1))) (Fin (fib (n - 1))) ℂ

end
