import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
import InfoGeometry.Quantum.AZDeclaredOneDimensionalTable

open InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
open InfoGeometry.Quantum.AZDeclaredOneDimensionalTable
open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge

namespace InfoGeometry.Quantum.AZDeclaredPeriodicTable

/-- Labels used in the declared dimension-indexed AZ table. -/
inductive PeriodicTableEntry : Type
  | zero
  | zModTwo
  | integers
  deriving DecidableEq

/-- The position of a spatial dimension on the eight-step Bott clock. -/
def bottClockResidue (d : ℕ) : ℕ :=
  d % 8

/-- Adding eight leaves the Bott-clock residue unchanged. -/
theorem bottClockResidue_add_eight (d : ℕ) :
    bottClockResidue (d + 8) = bottClockResidue d := by
  unfold bottClockResidue
  omega

/-- Convert the full table's group labels to this module's display labels. -/
def ofTopologicalGroup : TopologicalGroup → PeriodicTableEntry
  | .Zero => .zero
  | .Z2 => .zModTwo
  | .Z => .integers

/-- This view is definitionally derived from the single eight-periodic AZ
table, so the two table surfaces cannot silently drift apart. -/
def declaredPeriodicTableEntry (c : AZClass) (d : ℕ) : PeriodicTableEntry :=
  ofTopologicalGroup (azFullTable c d)

/-- The dimension-indexed display agrees with the independent one-dimensional
AZ row for every symmetry class. -/
theorem declaredOneDimensionalEntry_agrees (c : AZClass) :
    declaredPeriodicTableEntry c 1 =
      match declaredOneDimensionalEntry c with
      | .zero => .zero
      | .zModTwo => .zModTwo
      | .integers => .integers := by
  cases c <;> rfl

/-- The declared class-D, dimension-one entry is `zModTwo`. -/
theorem classD_dimensionOne_declared_entry :
    declaredPeriodicTableEntry AZClass.D 1 = .zModTwo := rfl

/-- The declared class-D, dimension-two entry is `integers`. -/
theorem classD_dimensionTwo_declared_entry :
    declaredPeriodicTableEntry AZClass.D 2 = .integers := rfl

/-- The declared one-dimensional BDI entry agrees with the 1D owner. -/
theorem classBDI_dimensionOne_declared_entry :
    declaredPeriodicTableEntry AZClass.BDI 1 = .integers := rfl

/-- The declared one-dimensional CII group is abstractly isomorphic to ℤ. -/
theorem classCII_dimensionOne_declared_entry :
    declaredPeriodicTableEntry AZClass.CII 1 = .integers := rfl

/-- The declared lookup table depends only on the dimension modulo eight. -/
theorem declaredPeriodicTableEntry_add_eight (c : AZClass) (d : ℕ) :
    declaredPeriodicTableEntry c (d + 8) = declaredPeriodicTableEntry c d := by
  simp [declaredPeriodicTableEntry, az_full_table_8fold_periodicity]

/-- Shifting an exponent by eight multiplies the corresponding power of two by 256. -/
theorem powerOfTwo_dimensionShiftEight (p q : ℕ) :
    2 ^ (p + 8 + q) = 2 ^ (p + q) * 256 := by
  have h : p + 8 + q = (p + q) + 8 := by ring
  rw [h, pow_add]
  rfl

end InfoGeometry.Quantum.AZDeclaredPeriodicTable
