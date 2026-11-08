import InfoGeometry.Algebra.CuntzN
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The Cuntz fixed-point criterion and a logarithmic dimension-candidate bound.
Neither an actual Hausdorff-dimension identification nor a G₂ contact grading
is inferred from these statements. A nonzero defect requires noncommutation.
-/

namespace InfoGeometry.Exceptional.SplitOctonionContactCantor

open InfoGeometry.Algebra.Cuntz

theorem triple_cantor_ratio_lt_two : (3 * Real.log 2) / Real.log 3 < 2 := by
  have hlog : Real.log ((2 : ℝ) ^ 3) < Real.log ((3 : ℝ) ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlog
  exact (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))).mpr (by
    simpa using hlog)

section Cuntz

variable {Carrier : Type*} [Ring Carrier] [StarRing Carrier] {branches : ℕ}
variable (family : CuntzNAlgebra (N := branches) Carrier)

def transfer (operator : Carrier) : Carrier :=
  ∑ index, family.S index * operator * star (family.S index)

theorem transfer_mul_generator (operator : Carrier) (index : Fin branches) :
    transfer family operator * family.S index = family.S index * operator := by
  simp [transfer, Finset.sum_mul, mul_assoc, family.isometry, mul_ite]

theorem transfer_one : transfer family 1 = 1 := by
  simpa [transfer] using family.range_sum

def transferHom : Carrier →+* Carrier where
  toFun := transfer family
  map_zero' := by simp [transfer]
  map_one' := transfer_one family
  map_add' first second := by simp [transfer, mul_add, add_mul, Finset.sum_add_distrib]
  map_mul' first second := by
    symm
    change transfer family first * (∑ index, family.S index * second * star (family.S index)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [← mul_assoc, ← mul_assoc, transfer_mul_generator]
    simp only [mul_assoc]

def defect_operator (operator : Carrier) : Carrier := operator - transfer family operator

theorem defect_vanishes_iff_commutes (operator : Carrier) :
    defect_operator family operator = 0 ↔
      ∀ index, operator * family.S index = family.S index * operator := by
  rw [defect_operator, sub_eq_zero]
  constructor
  · intro hfixed index
    calc
      operator * family.S index = transfer family operator * family.S index :=
        congrArg (fun value => value * family.S index) hfixed
      _ = family.S index * operator := transfer_mul_generator family operator index
  · intro hcommute
    symm
    calc
      transfer family operator = ∑ index, operator * (family.S index * star (family.S index)) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [← hcommute, mul_assoc]
      _ = operator * (∑ index, family.S index * star (family.S index)) :=
        (Finset.mul_sum _ _ _).symm
      _ = operator := by rw [family.range_sum, mul_one]

theorem defect_nonzero_iff (operator : Carrier) :
    defect_operator family operator ≠ 0 ↔
      ∃ index, operator * family.S index ≠ family.S index * operator := by
  simpa using not_congr (defect_vanishes_iff_commutes family operator)

theorem defect_one : defect_operator family 1 = 0 := by
  simp [defect_operator, transfer_one]

theorem transfer_preserves_star (operator : Carrier) :
    transfer family (star operator) = star (transfer family operator) := by
  simp [transfer, star_sum, star_mul, mul_assoc]

end Cuntz

end InfoGeometry.Exceptional.SplitOctonionContactCantor
