import Mathlib.Data.List.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Algebra.AnyonFiniteSpinBraid
import InfoGeometry.OperatorAlgebra.TripotentFactorization

/-!
# Witten-Möbius Braid Bridge

This module bridges the loxodromic Möbius reflection parity to the topological
braid system.

1. `braidWindingNumber`: Computes the total topological winding number of a braid word.
2. `IsEvenReflectionPairing`: States that each positive generator is balanced by a corresponding
   negative generator (the Witten parity cancellation).
3. `witten_reflection_winding_vanishes`: Proves that the total winding number of any
   braid word satisfying the even reflection pairing vanishes identically.

All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
-/

open InfoGeometry.Algebra.AnyonFiniteSpinBraid

namespace InfoGeometry.OperatorAlgebra.WittenMöbiusBraidBridge

variable {N : ℕ}

/-- The topological winding number of a braid word (a list of generator-sign pairs).
    `true` represents σ_i, `false` represents σ_i⁻¹. -/
def braidWindingNumber (word : List (ArtinGenerator N × Bool)) : ℤ :=
  (word.map (fun p => if p.2 then (1 : ℤ) else -1)).sum

/-- Predicate representing that a braid word is formed by even pairs of reflections
    (the number of positive generators matches the number of negative generators). -/
def IsEvenReflectionPairing (word : List (ArtinGenerator N × Bool)) : Prop :=
  (word.filter (fun p => p.2 = true)).length = (word.filter (fun p => p.2 = false)).length

theorem braidWindingNumber_eq_sub (word : List (ArtinGenerator N × Bool)) :
    braidWindingNumber word =
      ((word.filter (fun p => p.2 = true)).length : ℤ) -
      ((word.filter (fun p => p.2 = false)).length : ℤ) := by
  induction' word with p tail ih
  · simp [braidWindingNumber]
  · rcases p with ⟨i, b⟩
    cases b
    · dsimp [braidWindingNumber] at ih ⊢
      have h1 : (List.filter (fun p => p.snd = true) ((i, false) :: tail)).length =
          (List.filter (fun p => p.snd = true) tail).length := rfl
      have h2 : (List.filter (fun p => p.snd = false) ((i, false) :: tail)).length =
          (List.filter (fun p => p.snd = false) tail).length + 1 := rfl
      rw [h1, h2, ih]
      omega
    · dsimp [braidWindingNumber] at ih ⊢
      have h1 : (List.filter (fun p => p.snd = true) ((i, true) :: tail)).length =
          (List.filter (fun p => p.snd = true) tail).length + 1 := rfl
      have h2 : (List.filter (fun p => p.snd = false) ((i, true) :: tail)).length =
          (List.filter (fun p => p.snd = false) tail).length := rfl
      rw [h1, h2, ih]
      omega

/-- Theorem: For any braid word satisfying the even reflection pairing (Witten cancellation),
    the total topological winding number vanishes. -/
theorem witten_reflection_winding_vanishes (word : List (ArtinGenerator N × Bool))
    (h : IsEvenReflectionPairing word) :
    braidWindingNumber word = 0 := by
  rw [braidWindingNumber_eq_sub, h, sub_self]

end InfoGeometry.OperatorAlgebra.WittenMöbiusBraidBridge
