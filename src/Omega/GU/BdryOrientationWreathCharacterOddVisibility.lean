/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Int.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.GU.BdryOrientationBlockDecompositionOddVisibility
import Omega.GU.BdryZ2JumpUniqueness

namespace Omega.GU

/-- The sign of the permutation induced on the odd-cardinality blocks. -/
def oddBlockPermutationSign {T : Type*} [Fintype T] [DecidableEq T] (size : T → ℕ)
    (tau : Equiv.Perm T) : Units ℤ :=
  if ∀ t, Odd (size t) then tau.sign else 1

/-- The global wreath orientation character on the boundary labeling torsor. -/
def wreathOrientationSign {T : Type*} [Fintype T] [DecidableEq T] (size : T → ℕ)
    (eps : T → Units ℤ) (tau : Equiv.Perm T) : Units ℤ :=
  if oddBlockPermutationSign size tau = 1 then Finset.univ.prod eps
  else -(Finset.univ.prod eps)

/-- The odd-block visibility decomposition makes the wreath orientation character split into the
odd-block permutation sign and the product of the blockwise signs.
`thm:bdry-orientation-wreath-character-odd-visibility` -/
theorem paper_bdry_orientation_wreath_character_odd_visibility {T : Type} [Fintype T]
    [DecidableEq T] (size : T → Nat) (eps : T → Units Int) (tau : Equiv.Perm T) :
    wreathOrientationSign size eps tau = oddBlockPermutationSign size tau * Finset.univ.prod eps := by
  have hsign : oddBlockPermutationSign size tau = 1 ∨
      oddBlockPermutationSign size tau = -1 := by
    by_cases hOdd : ∀ t, Odd (size t)
    · simpa [oddBlockPermutationSign, hOdd] using Int.units_eq_one_or (tau.sign)
    · simp [oddBlockPermutationSign, hOdd]
  unfold wreathOrientationSign
  split_ifs with h
  · simp [h]
  · rcases hsign with hOne | hNeg
    · exact (h hOne).elim
    · rw [hNeg]
      simp

end Omega.GU
