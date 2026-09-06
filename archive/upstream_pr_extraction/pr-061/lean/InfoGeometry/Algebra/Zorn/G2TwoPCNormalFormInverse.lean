import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

namespace InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

abbrev PCInverse := PCExponent → PCExponent

lemma F2_two_eq_zero : (2 : F2) = 0 := by
  simpa using (F2_mul_two (1 : F2))

def pcInverse (e : PCExponent) : PCExponent
  | 0 => e 0
  | 1 => e 1
  | 2 => (e 0 && e 1) ^^ e 2
  | 3 => (e 0 && e 1) ^^ (e 0 && e 4) ^^ e 3
  | 4 => e 4
  | 5 => (e 0 && e 1 && e 2) ^^ (e 0 && e 1) ^^ (e 0 && e 2) ^^ (e 1 && e 3) ^^
      (e 1 && e 4) ^^ e 1 ^^ (e 2 && e 4) ^^ e 2 ^^ e 5

theorem pcInverse_apply_zero (e : PCExponent) :
    pcInverse e 0 = e 0 := rfl

theorem pcInverse_apply_one (e : PCExponent) :
    pcInverse e 1 = e 1 := rfl

theorem pcInverse_apply_two (e : PCExponent) :
    pcInverse e 2 = ((e 0 && e 1) ^^ e 2) := rfl

theorem pcInverse_apply_three (e : PCExponent) :
    pcInverse e 3 = ((e 0 && e 1) ^^ (e 0 && e 4) ^^ e 3) := rfl

theorem pcInverse_apply_four (e : PCExponent) :
    pcInverse e 4 = e 4 := rfl

theorem pcCombine_inverse_apply_zero (e : PCExponent) :
    pcCombine e (pcInverse e) 0 = false := by
  simp [pcCombine, pcInverse]

theorem pcCombine_inverse_apply_one (e : PCExponent) :
    pcCombine e (pcInverse e) 1 = false := by
  simp [pcCombine, pcInverse]

theorem pcCombine_inverse_apply_two (e : PCExponent) :
    pcCombine e (pcInverse e) 2 = false := by
  rw [← bitToF2_eq_iff]
  simp only [pcCombine, pcInverse, bitToF2_xor, bitToF2_and]
  ring_nf
  simp [F2_two_eq_zero]
  change (0 : F2) = 0
  rfl

theorem pcCombine_inverse_apply_three (e : PCExponent) :
    pcCombine e (pcInverse e) 3 = false := by
  rw [← bitToF2_eq_iff]
  simp only [pcCombine, pcInverse, bitToF2_xor, bitToF2_and]
  ring_nf
  simp [F2_two_eq_zero]
  change (0 : F2) = 0
  rfl

theorem pcCombine_inverse_apply_four (e : PCExponent) :
    pcCombine e (pcInverse e) 4 = false := by
  simp [pcCombine, pcInverse]

theorem pcCombine_inverse_apply_five (e : PCExponent) :
    pcCombine e (pcInverse e) 5 = false := by
  rw [← bitToF2_eq_iff]
  simp only [pcCombine, pcInverse, bitToF2_xor, bitToF2_and]
  ring_nf
  simp [F2_two_eq_zero, F2_mul_four]
  change (0 : F2) = 0
  rfl

theorem pcCombine_right_inverse (e : PCExponent) :
    pcCombine e (pcInverse e) = zeroPC := by
  funext i
  fin_cases i
  · exact pcCombine_inverse_apply_zero e
  · exact pcCombine_inverse_apply_one e
  · exact pcCombine_inverse_apply_two e
  · exact pcCombine_inverse_apply_three e
  · exact pcCombine_inverse_apply_four e
  · exact pcCombine_inverse_apply_five e

theorem pcCombine_left_inverse_apply_zero (e : PCExponent) :
    pcCombine (pcInverse e) e 0 = false := by
  simp [pcCombine, pcInverse]

theorem pcCombine_left_inverse_apply_one (e : PCExponent) :
    pcCombine (pcInverse e) e 1 = false := by
  simp [pcCombine, pcInverse]

theorem pcCombine_left_inverse_apply_four (e : PCExponent) :
    pcCombine (pcInverse e) e 4 = false := by
  simp [pcCombine, pcInverse]

theorem pcCombine_left_inverse_apply_two (e : PCExponent) :
    pcCombine (pcInverse e) e 2 = false := by
  rw [← bitToF2_eq_iff]
  simp only [pcCombine, pcInverse, bitToF2_xor, bitToF2_and]
  ring_nf
  simp [F2_two_eq_zero]
  change (0 : F2) = 0
  rfl

theorem pcCombine_left_inverse_apply_three (e : PCExponent) :
    pcCombine (pcInverse e) e 3 = false := by
  rw [← bitToF2_eq_iff]
  simp only [pcCombine, pcInverse, bitToF2_xor, bitToF2_and]
  ring_nf
  simp [F2_two_eq_zero]
  change (0 : F2) = 0
  rfl

theorem pcCombine_left_inverse_apply_five (e : PCExponent) :
    pcCombine (pcInverse e) e 5 = false := by
  rw [← bitToF2_eq_iff]
  simp only [pcCombine, pcInverse, bitToF2_xor, bitToF2_and]
  ring_nf
  simp [F2_two_eq_zero, F2_mul_four]
  rw [show bitToF2 false = 0 by rfl]
  ring
  change (0 : F2) = 0
  rfl

theorem pcCombine_left_inverse (e : PCExponent) :
    pcCombine (pcInverse e) e = zeroPC := by
  funext i
  fin_cases i
  · exact pcCombine_left_inverse_apply_zero e
  · exact pcCombine_left_inverse_apply_one e
  · exact pcCombine_left_inverse_apply_two e
  · exact pcCombine_left_inverse_apply_three e
  · exact pcCombine_left_inverse_apply_four e
  · exact pcCombine_left_inverse_apply_five e

end InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
