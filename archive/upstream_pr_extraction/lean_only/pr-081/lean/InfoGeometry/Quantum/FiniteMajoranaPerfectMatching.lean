import InfoGeometry.Quantum.FiniteMajoranaPairingBlocks
import Mathlib.Tactic

/-!
# Canonical finite Majorana perfect matching

This file supplies the combinatorial object behind the block product: a
perfect matching is an involution without fixed points.  The canonical
matching pairs the two Majorana labels in each finite block.  No general
Pfaffian expansion is asserted here.
-/

namespace InfoGeometry.Quantum.FiniteMajoranaPerfectMatching

open InfoGeometry.Quantum.FiniteMajoranaPairingBlocks

abbrev MajoranaLabel (N : ℕ) := Fin N × Fin 2

/-- Swap the two labels inside one Majorana pair. -/
def pairSwap (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

theorem pairSwap_involutive (i : Fin 2) :
    pairSwap (pairSwap i) = i := by
  fin_cases i <;> simp [pairSwap]

theorem pairSwap_ne (i : Fin 2) : pairSwap i ≠ i := by
  fin_cases i <;> simp [pairSwap]

/-- A finite perfect matching represented by its partner involution. -/
structure PerfectMatching (α : Type*) where
  partner : α → α
  partner_involutive : Function.Involutive partner
  partner_ne : ∀ x, partner x ≠ x

/-- The canonical matching of the two Majorana labels in every block. -/
def canonicalMatching (N : ℕ) : PerfectMatching (MajoranaLabel N) where
  partner p := (p.1, pairSwap p.2)
  partner_involutive p := by
    ext <;> simp [pairSwap_involutive]
  partner_ne p := by
    intro h
    have h₂ : pairSwap p.2 = p.2 := congrArg Prod.snd h
    exact (pairSwap_ne p.2) h₂

/-- The canonical matching has exactly one edge for each block label. -/
def matchingWeight {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∏ k, a k

theorem canonicalMatching_weight_squared_eq_blockDeterminant
    {N : ℕ} (a : Fin N → ℝ) :
    (matchingWeight a) ^ 2 = finitePairingDeterminant a := by
  symm
  exact finitePairingDeterminant_eq_square a

end InfoGeometry.Quantum.FiniteMajoranaPerfectMatching
