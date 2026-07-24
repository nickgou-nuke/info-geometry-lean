import Mathlib
import InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge

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

/-- Declared periodic-table data; this is not a stable-phase classification. -/
def declaredPeriodicTableEntry (c : AZClass) (d : ℕ) : PeriodicTableEntry :=
  match c, bottClockResidue d with
  | AZClass.A, 0 | AZClass.A, 2 | AZClass.A, 4 | AZClass.A, 6 => .integers
  | AZClass.AIII, 1 | AZClass.AIII, 3 | AZClass.AIII, 5 | AZClass.AIII, 7 => .integers
  | AZClass.D, 0 | AZClass.D, 1 => .zModTwo
  | AZClass.D, 2 => .integers
  | AZClass.BDI, 0 => .integers
  | AZClass.BDI, 1 | AZClass.BDI, 2 => .zModTwo
  | AZClass.BDI, 3 => .integers
  | AZClass.DIII, 1 | AZClass.DIII, 2 => .zModTwo
  | AZClass.DIII, 3 => .integers
  | _, _ => .zero

/-- The declared class-D, dimension-one entry is `zModTwo`. -/
theorem classD_dimensionOne_declared_entry :
    declaredPeriodicTableEntry AZClass.D 1 = .zModTwo := rfl

/-- The declared class-D, dimension-two entry is `integers`. -/
theorem classD_dimensionTwo_declared_entry :
    declaredPeriodicTableEntry AZClass.D 2 = .integers := rfl

/-- The declared lookup table depends only on the dimension modulo eight. -/
theorem declaredPeriodicTableEntry_add_eight (c : AZClass) (d : ℕ) :
    declaredPeriodicTableEntry c (d + 8) = declaredPeriodicTableEntry c d := by
  unfold declaredPeriodicTableEntry
  rw [bottClockResidue_add_eight]

/-- Shifting an exponent by eight multiplies the corresponding power of two by 256. -/
theorem powerOfTwo_dimensionShiftEight (p q : ℕ) :
    2 ^ (p + 8 + q) = 2 ^ (p + q) * 256 := by
  have h : p + 8 + q = (p + q) + 8 := by ring
  rw [h, pow_add]
  rfl

end InfoGeometry.Quantum.AZDeclaredPeriodicTable
