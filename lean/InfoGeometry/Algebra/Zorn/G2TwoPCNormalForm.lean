import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

namespace InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

abbrev PCExponent := Fin 6 → Bool

def pcCombine (e f : PCExponent) : PCExponent
  | 0 => e 0 ^^ f 0
  | 1 => e 1 ^^ f 1
  | 2 => (e 1 && f 0) ^^ e 2 ^^ f 2
  | 3 => (e 1 && f 0) ^^ e 3 ^^ (e 4 && f 0) ^^ f 3
  | 4 => e 4 ^^ f 4
  | 5 => (e 1 && e 2 && f 0) ^^ (e 1 && f 0 && f 1) ^^
      (e 1 && f 0 && f 2) ^^ (e 1 && f 0) ^^ (e 1 && f 1) ^^ (e 2 && f 0) ^^
      (e 2 && f 2) ^^ (e 3 && f 1) ^^ (e 4 && f 0 && f 1) ^^
      (e 4 && f 1) ^^ (e 4 && f 2) ^^ e 5 ^^ f 5

def zeroPC : PCExponent := fun _ => false

theorem pcCombine_zero_left (e : PCExponent) :
    pcCombine zeroPC e = e := by
  funext i
  fin_cases i <;> simp [pcCombine, zeroPC]

theorem pcCombine_zero_right (e : PCExponent) :
    pcCombine e zeroPC = e := by
  funext i
  fin_cases i <;> simp [pcCombine, zeroPC]

theorem pcCombine_apply_zero (e f : PCExponent) :
    pcCombine e f 0 = (e 0 ^^ f 0) := rfl

theorem pcCombine_apply_one (e f : PCExponent) :
    pcCombine e f 1 = (e 1 ^^ f 1) := rfl

theorem pcCombine_apply_two (e f : PCExponent) :
    pcCombine e f 2 = ((e 1 && f 0) ^^ e 2 ^^ f 2) := rfl

theorem pcCombine_apply_three (e f : PCExponent) :
    pcCombine e f 3 =
      ((e 1 && f 0) ^^ e 3 ^^ (e 4 && f 0) ^^ f 3) := rfl

theorem pcCombine_apply_four (e f : PCExponent) :
    pcCombine e f 4 = (e 4 ^^ f 4) := rfl

theorem pcCombine_apply_five (e f : PCExponent) :
    pcCombine e f 5 =
      ((e 1 && e 2 && f 0) ^^ (e 1 && f 0 && f 1) ^^
        (e 1 && f 0 && f 2) ^^ (e 1 && f 0) ^^ (e 1 && f 1) ^^
        (e 2 && f 0) ^^ (e 2 && f 2) ^^ (e 3 && f 1) ^^
        (e 4 && f 0 && f 1) ^^ (e 4 && f 1) ^^ (e 4 && f 2) ^^ e 5 ^^ f 5) := rfl

theorem bitToF2_pcCombine_apply_two (e f : PCExponent) :
    bitToF2 (pcCombine e f 2) =
      bitToF2 (e 1) * bitToF2 (f 0) +
        bitToF2 (e 2) + bitToF2 (f 2) := by
  rw [pcCombine_apply_two, bitToF2_xor, bitToF2_xor, bitToF2_and]

theorem bitToF2_pcCombine_apply_zero (e f : PCExponent) :
    bitToF2 (pcCombine e f 0) =
      bitToF2 (e 0) + bitToF2 (f 0) := by
  rw [pcCombine_apply_zero, bitToF2_xor]

theorem bitToF2_pcCombine_apply_one (e f : PCExponent) :
    bitToF2 (pcCombine e f 1) =
      bitToF2 (e 1) + bitToF2 (f 1) := by
  rw [pcCombine_apply_one, bitToF2_xor]

theorem bitToF2_pcCombine_apply_four (e f : PCExponent) :
    bitToF2 (pcCombine e f 4) =
      bitToF2 (e 4) + bitToF2 (f 4) := by
  rw [pcCombine_apply_four, bitToF2_xor]

theorem bitToF2_pcCombine_apply_three (e f : PCExponent) :
    bitToF2 (pcCombine e f 3) =
      bitToF2 (e 1) * bitToF2 (f 0) + bitToF2 (e 3) +
        bitToF2 (e 4) * bitToF2 (f 0) + bitToF2 (f 3) := by
  rw [pcCombine_apply_three]
  simp only [bitToF2_xor, bitToF2_and]

theorem bitToF2_pcCombine_apply_five (e f : PCExponent) :
    bitToF2 (pcCombine e f 5) =
      bitToF2 (e 1) * bitToF2 (e 2) * bitToF2 (f 0) +
        bitToF2 (e 1) * bitToF2 (f 0) * bitToF2 (f 1) +
        bitToF2 (e 1) * bitToF2 (f 0) * bitToF2 (f 2) +
        bitToF2 (e 1) * bitToF2 (f 0) +
        bitToF2 (e 1) * bitToF2 (f 1) +
        bitToF2 (e 2) * bitToF2 (f 0) +
        bitToF2 (e 2) * bitToF2 (f 2) +
        bitToF2 (e 3) * bitToF2 (f 1) +
        bitToF2 (e 4) * bitToF2 (f 0) * bitToF2 (f 1) +
        bitToF2 (e 4) * bitToF2 (f 1) +
        bitToF2 (e 4) * bitToF2 (f 2) +
      bitToF2 (e 5) + bitToF2 (f 5) := by
  rw [pcCombine_apply_five]
  simp only [bitToF2_xor, bitToF2_and]

end InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
