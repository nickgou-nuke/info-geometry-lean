/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
import InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
import InfoGeometry.Quantum.AZDeclaredOneDimensionalTable

open InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
open InfoGeometry.Quantum.AZTenFoldFullPeriodicTable
open InfoGeometry.Quantum.AZDeclaredOneDimensionalTable

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

/-- Convert the canonical full-table labels to the compact display labels. -/
def ofTopologicalGroup : TopologicalGroup → PeriodicTableEntry
  | .Zero => .zero
  | .Z2 => .zModTwo
  | .Z => .integers

/-- Display view of the canonical Bott-index table. This definition shares the
same classifier as the finite-matrix/operator lanes. -/
def declaredPeriodicTableEntry (c : AZClass) (d : ℕ) : PeriodicTableEntry :=
  ofTopologicalGroup (azFullTable c d)

/-- The dimension-one display agrees with the existing one-dimensional AZ owner. -/
theorem declaredOneDimensionalEntry_agrees (c : AZClass) :
    declaredPeriodicTableEntry c 1 =
      match declaredOneDimensionalEntry c with
      | .zero => .zero
      | .zModTwo => .zModTwo
      | .integers => .integers := by
  cases c <;>
    simp [declaredPeriodicTableEntry, ofTopologicalGroup, azFullTable,
      azBottIndex, complexKSpaceLabel, realKSpaceLabel,
      declaredOneDimensionalEntry]

/-- The declared class-D, dimension-one entry is `zModTwo`. -/
theorem classD_dimensionOne_declared_entry :
    declaredPeriodicTableEntry AZClass.D 1 = .zModTwo := rfl

/-- The declared class-D, dimension-two entry is `integers`. -/
theorem classD_dimensionTwo_declared_entry :
    declaredPeriodicTableEntry AZClass.D 2 = .integers := rfl

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
