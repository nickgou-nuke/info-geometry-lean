import Mathlib.Data.List.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Algebra.AnyonFiniteSpinBraid

open InfoGeometry.Algebra.AnyonFiniteSpinBraid

namespace InfoGeometry.OperatorAlgebra.WittenMobiusBraidBridge

variable {N : ℕ}

/-- Signed winding of a finite Artin braid word. -/
def braidWindingNumber (word : List (ArtinGenerator N × Bool)) : ℤ :=
  (word.map (fun p => if p.2 then (1 : ℤ) else -1)).sum

/-- A word has balanced positive and negative reflection generators. -/
def IsEvenReflectionPairing (word : List (ArtinGenerator N × Bool)) : Prop :=
  (word.filter (fun p => p.2 = true)).length =
    (word.filter (fun p => p.2 = false)).length

theorem braidWindingNumber_eq_sub (word : List (ArtinGenerator N × Bool)) :
    braidWindingNumber word =
      ((word.filter (fun p => p.2 = true)).length : ℤ) -
      ((word.filter (fun p => p.2 = false)).length : ℤ) := by
  induction' word with p tail ih
  · simp [braidWindingNumber]
  · rcases p with ⟨i, b⟩
    cases b
    · dsimp [braidWindingNumber] at ih ⊢
      rw [show (List.filter (fun p => p.snd = true) ((i, false) :: tail)).length =
          (List.filter (fun p => p.snd = true) tail).length by rfl]
      rw [show (List.filter (fun p => p.snd = false) ((i, false) :: tail)).length =
          (List.filter (fun p => p.snd = false) tail).length + 1 by rfl]
      rw [ih]
      omega
    · dsimp [braidWindingNumber] at ih ⊢
      rw [show (List.filter (fun p => p.snd = true) ((i, true) :: tail)).length =
          (List.filter (fun p => p.snd = true) tail).length + 1 by rfl]
      rw [show (List.filter (fun p => p.snd = false) ((i, true) :: tail)).length =
          (List.filter (fun p => p.snd = false) tail).length by rfl]
      rw [ih]
      omega

theorem witten_reflection_winding_vanishes
    (word : List (ArtinGenerator N × Bool))
    (h : IsEvenReflectionPairing word) :
    braidWindingNumber word = 0 := by
  rw [braidWindingNumber_eq_sub, h, sub_self]

end InfoGeometry.OperatorAlgebra.WittenMobiusBraidBridge
