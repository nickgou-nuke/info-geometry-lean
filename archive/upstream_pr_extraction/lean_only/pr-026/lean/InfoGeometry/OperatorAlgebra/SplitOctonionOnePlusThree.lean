import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Split-octonion `1 + 3` slot layer

This module is the Lean twin of
`tools/sympy/split_octonion_one_plus_three_slots.py`.

It packages the finite `1 + 3` Zorn basis-slot laws that sit above the true
split-octonion multiplication table:

* diagonal idempotents `ePlus`, `eMinus`;
* three upper vector slots `up i` and three lower vector slots `down i`;
* diagonal absorption/annihilation laws;
* paired upper/lower readback to diagonal idempotents;
* cyclic slot multiplication table.

This is an algebraic basis-slot theorem surface only.  It does not assert a
`G₂(2)` automorphism theorem, an `SU(3)` stabilizer theorem, or a particle
classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.OnePlusThree

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Three finite vector slots used by the Zorn `1 + 3` decomposition. -/
abbrev ColorSlot := Fin 3

/-- Positive diagonal scalar/idempotent slot. -/
def scalarPlus : SplitOct := ePlus

/-- Negative diagonal scalar/idempotent slot. -/
def scalarMinus : SplitOct := eMinus

/-- Upper `3`-slot readout. -/
def upperSlot (i : ColorSlot) : SplitOct := up i

/-- Lower `3`-slot readout. -/
def lowerSlot (i : ColorSlot) : SplitOct := down i

/-- The two scalar slots are idempotent and mutually orthogonal. -/
theorem scalar_slots_orthogonal_idempotents :
    mulZ scalarPlus scalarPlus = scalarPlus ∧
      mulZ scalarMinus scalarMinus = scalarMinus ∧
      mulZ scalarPlus scalarMinus = zeroZ ∧
      mulZ scalarMinus scalarPlus = zeroZ := by
  exact ⟨ePlus_idempotent, eMinus_idempotent, ePlus_mul_eMinus, eMinus_mul_ePlus⟩

/-- The positive diagonal slot absorbs upper slots from the left and annihilates lower slots. -/
theorem scalarPlus_left_action (i : ColorSlot) :
    mulZ scalarPlus (upperSlot i) = upperSlot i ∧
      mulZ scalarPlus (lowerSlot i) = zeroZ := by
  exact ⟨ePlus_mul_up i, ePlus_mul_down_zero i⟩

/-- The negative diagonal slot absorbs lower slots from the left and annihilates upper slots. -/
theorem scalarMinus_left_action (i : ColorSlot) :
    mulZ scalarMinus (lowerSlot i) = lowerSlot i ∧
      mulZ scalarMinus (upperSlot i) = zeroZ := by
  exact ⟨eMinus_mul_down i, eMinus_mul_up_zero i⟩

/-- Upper slots absorb the negative diagonal on the right and annihilate the positive diagonal. -/
theorem upperSlot_right_action (i : ColorSlot) :
    mulZ (upperSlot i) scalarMinus = upperSlot i ∧
      mulZ (upperSlot i) scalarPlus = zeroZ := by
  exact ⟨up_mul_eMinus i, up_mul_ePlus_zero i⟩

/-- Lower slots absorb the positive diagonal on the right and annihilate the negative diagonal. -/
theorem lowerSlot_right_action (i : ColorSlot) :
    mulZ (lowerSlot i) scalarPlus = lowerSlot i ∧
      mulZ (lowerSlot i) scalarMinus = zeroZ := by
  exact ⟨down_mul_ePlus i, down_mul_eMinus_zero i⟩

/-- Matching upper/lower slots read back the positive diagonal idempotent. -/
theorem upper_lower_same_reads_scalarPlus (i : ColorSlot) :
    mulZ (upperSlot i) (lowerSlot i) = scalarPlus := by
  exact up_mul_down_same i

/-- Matching lower/upper slots read back the negative diagonal idempotent. -/
theorem lower_upper_same_reads_scalarMinus (i : ColorSlot) :
    mulZ (lowerSlot i) (upperSlot i) = scalarMinus := by
  exact down_mul_up_same i

/-- Upper and lower vector slots are nil-square and split-null for `detZ`. -/
theorem vector_slots_nil_and_null (i : ColorSlot) :
    mulZ (upperSlot i) (upperSlot i) = zeroZ ∧
      mulZ (lowerSlot i) (lowerSlot i) = zeroZ ∧
      detZ (upperSlot i) = 0 ∧
      detZ (lowerSlot i) = 0 := by
  exact ⟨up_sq_zero i, down_sq_zero i, detZ_up i, detZ_down i⟩

/-- Cyclic upper-slot products close into the lower `3`-slot. -/
theorem upper_cyclic_slot_table :
    mulZ (upperSlot 0) (upperSlot 1) = lowerSlot 2 ∧
      mulZ (upperSlot 1) (upperSlot 2) = lowerSlot 0 ∧
      mulZ (upperSlot 2) (upperSlot 0) = lowerSlot 1 := by
  exact ⟨up0_mul_up1, up1_mul_up2, up2_mul_up0⟩

/-- Reversed upper-slot products carry the opposite sign. -/
theorem upper_reversed_slot_table :
    mulZ (upperSlot 1) (upperSlot 0) = negZ (lowerSlot 2) ∧
      mulZ (upperSlot 2) (upperSlot 1) = negZ (lowerSlot 0) ∧
      mulZ (upperSlot 0) (upperSlot 2) = negZ (lowerSlot 1) := by
  exact ⟨up1_mul_up0, up2_mul_up1, up0_mul_up2⟩

/-- Cyclic lower-slot products close into the negative upper `3`-slot. -/
theorem lower_cyclic_slot_table :
    mulZ (lowerSlot 0) (lowerSlot 1) = negZ (upperSlot 2) ∧
      mulZ (lowerSlot 1) (lowerSlot 2) = negZ (upperSlot 0) ∧
      mulZ (lowerSlot 2) (lowerSlot 0) = negZ (upperSlot 1) := by
  exact ⟨down0_mul_down1, down1_mul_down2, down2_mul_down0⟩

/-- Reversed lower-slot products carry the opposite sign. -/
theorem lower_reversed_slot_table :
    mulZ (lowerSlot 1) (lowerSlot 0) = upperSlot 2 ∧
      mulZ (lowerSlot 2) (lowerSlot 1) = upperSlot 0 ∧
      mulZ (lowerSlot 0) (lowerSlot 2) = upperSlot 1 := by
  exact ⟨down1_mul_down0, down2_mul_down1, down0_mul_down2⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.OnePlusThree
