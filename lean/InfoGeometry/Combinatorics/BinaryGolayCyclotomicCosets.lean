import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace InfoGeometry.Combinatorics.BinaryGolayCyclotomicCosets

def quadraticResidueCoset : Finset ℕ :=
  {1, 2, 4, 8, 16, 9, 18, 13, 3, 6, 12}

def nonResidueCoset : Finset ℕ :=
  {5, 10, 20, 17, 11, 22, 21, 19, 15, 7, 14}

def doubleMod23 (k : ℕ) : ℕ := 2 * k % 23

theorem two_pow_eleven_mod_23 : 2 ^ 11 % 23 = 1 := by
  norm_num

theorem quadraticResidueCoset_card : quadraticResidueCoset.card = 11 := by
  decide

theorem nonResidueCoset_card : nonResidueCoset.card = 11 := by
  decide

theorem cosets_disjoint : Disjoint quadraticResidueCoset nonResidueCoset := by
  decide

theorem cosets_cover_nonzero_mod_23 :
    quadraticResidueCoset ∪ nonResidueCoset = Finset.Icc 1 22 := by
  decide

theorem quadraticResidueCoset_double_closed :
    quadraticResidueCoset.image doubleMod23 = quadraticResidueCoset := by
  decide

theorem nonResidueCoset_double_closed :
    nonResidueCoset.image doubleMod23 = nonResidueCoset := by
  decide

end InfoGeometry.Combinatorics.BinaryGolayCyclotomicCosets
