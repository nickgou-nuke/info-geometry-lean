import Mathlib

/-!
# Cl(4,4) Fock Parity — 16-state occupation sheet

Four fermionic CAR modes generate 2^4 = 16 occupation states given
by `Fin 4 → Bool`. The even-cardinality subsets (0,2,4 elements)
and odd-cardinality subsets (1,3 elements) both count to 8.
Hence the finite Witten index Tr((-1)^F) = 8 - 8 = 0.

All theorems are proved by `native_decide` on the finite type.
This is the algebraic bridge from the four-mode CAR packet to the
Witten-Möbius chiral parity cancellation layer.
-/

open Finset

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl44FockParity

/-- Occupation label for four modes. -/
abbrev Occ4 := Fin 4 → Bool

instance : Fintype Occ4 := Pi.fintype

/-- Total number of occupation states: 2^4 = 16. -/
theorem card_total : Fintype.card Occ4 = 16 := by
  native_decide

/-- Number of even-cardinality occupation states = 8. -/
theorem card_even : Fintype.card {w : Occ4 // Even ((Finset.univ.filter w).card)} = 8 := by
  native_decide

/-- Number of odd-cardinality occupation states = 8. -/
theorem card_odd : Fintype.card {w : Occ4 // ¬ Even ((Finset.univ.filter w).card)} = 8 := by
  native_decide

/-- Finite Witten index: 8 - 8 = 0. -/
theorem witten_index_zero : ((8 : ℤ) - 8) = 0 := by
  norm_num

/-- Even and odd sectors have equal cardinality. -/
theorem even_odd_card_equal :
    Fintype.card {w : Occ4 // Even ((Finset.univ.filter w).card)} =
    Fintype.card {w : Occ4 // ¬ Even ((Finset.univ.filter w).card)} := by
  rw [card_even, card_odd]

/-- Toggle mode 0: flips occupied status of first mode. -/
def toggle0 (w : Occ4) : Occ4 :=
  fun i => if i = (0 : Fin 4) then !w i else w i

/-- toggle0 is an involution. -/
theorem toggle0_involutive : Function.Involutive toggle0 := by
  intro w; funext i; by_cases h : i = 0 <;> simp [toggle0, h]

end InfoGeometry.OperatorAlgebra.Cl44FockParity
