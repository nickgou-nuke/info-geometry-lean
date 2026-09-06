import InfoGeometry.Algebra.FiveGradedTKK

/-!
# Cyclotomic quotient of the five TKK weights

The TKK owner supplies the five integer weights `-2,-1,0,1,2`.
This file records only their reduction modulo three.  It does not add a
bracket, a Lie-algebra instance, or a covering-group interpretation.
-/

namespace InfoGeometry.Canonical.TKKFiveGradeCyclotomicQuotient

open InfoGeometry.Algebra.FiveGradedTKK

/-- The order-three residue carried by a five-grade TKK label. -/
def weight5Residue (k : Weight5) : ZMod 3 := Weight5.toInt k

@[simp] theorem weight5Residue_neg_two :
    weight5Residue Weight5.neg_two = 1 := by
  change ((-2 : ℤ) : ZMod 3) = 1
  decide

@[simp] theorem weight5Residue_neg_one :
    weight5Residue Weight5.neg_one = 2 := by
  change ((-1 : ℤ) : ZMod 3) = 2
  decide

@[simp] theorem weight5Residue_zero :
    weight5Residue Weight5.zero = 0 := by
  rfl

@[simp] theorem weight5Residue_pos_one :
    weight5Residue Weight5.pos_one = 1 := by
  norm_num [weight5Residue, Weight5.toInt]

@[simp] theorem weight5Residue_pos_two :
    weight5Residue Weight5.pos_two = 2 := by
  norm_num [weight5Residue, Weight5.toInt]

/-- The opposite of a five-grade label. -/
def weight5Opposite : Weight5 → Weight5
  | .neg_two => .pos_two
  | .neg_one => .pos_one
  | .zero => .zero
  | .pos_one => .neg_one
  | .pos_two => .neg_two

@[simp] theorem weight5Opposite_toInt (k : Weight5) :
    Weight5.toInt (weight5Opposite k) = -Weight5.toInt k := by
  cases k <;> rfl

@[simp] theorem weight5Residue_opposite (k : Weight5) :
    weight5Residue (weight5Opposite k) = -weight5Residue k := by
  change (Weight5.toInt (weight5Opposite k) : ZMod 3) =
    -(Weight5.toInt k : ZMod 3)
  rw [weight5Opposite_toInt]
  simp

/-- Integer degree resonance descends to zero cyclotomic degree. -/
theorem weight5_resonance_residue_zero
    (k l : Weight5)
    (h : Weight5.toInt k + Weight5.toInt l = 0) :
    weight5Residue k + weight5Residue l = 0 := by
  change (Weight5.toInt k : ZMod 3) +
      (Weight5.toInt l : ZMod 3) = 0
  rw [← Int.cast_add]
  simpa using congrArg (fun n : ℤ => (n : ZMod 3)) h

/-- The residue of a sum of integer TKK degrees is the sum of residues. -/
theorem integer_degree_residue_add (m n : ℤ) :
    ((m + n : ℤ) : ZMod 3) = (m : ZMod 3) + (n : ZMod 3) := by
  simp

end InfoGeometry.Canonical.TKKFiveGradeCyclotomicQuotient
