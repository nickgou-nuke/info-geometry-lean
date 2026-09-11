import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

namespace InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

theorem pcCombine_assoc_zero (e f g : PCExponent) :
    pcCombine (pcCombine e f) g 0 =
      pcCombine e (pcCombine f g) 0 := by
  simp [pcCombine]

theorem pcCombine_assoc_one (e f g : PCExponent) :
    pcCombine (pcCombine e f) g 1 =
      pcCombine e (pcCombine f g) 1 := by
  simp [pcCombine]

theorem pcCombine_assoc_two (e f g : PCExponent) :
    pcCombine (pcCombine e f) g 2 =
      pcCombine e (pcCombine f g) 2 := by
  simp only [pcCombine]
  rw [← bitToF2_eq_iff]
  simp only [bitToF2_xor, bitToF2_and]
  ring

theorem pcCombine_assoc_three (e f g : PCExponent) :
    pcCombine (pcCombine e f) g 3 =
      pcCombine e (pcCombine f g) 3 := by
  simp only [pcCombine]
  rw [← bitToF2_eq_iff]
  simp only [bitToF2_xor, bitToF2_and]
  ring

theorem pcCombine_assoc_four (e f g : PCExponent) :
    pcCombine (pcCombine e f) g 4 =
      pcCombine e (pcCombine f g) 4 := by
  simp [pcCombine]

theorem pcCombine_assoc_five (e f g : PCExponent) :
    pcCombine (pcCombine e f) g 5 =
      pcCombine e (pcCombine f g) 5 := by
  simp only [pcCombine]
  rw [← bitToF2_eq_iff]
  simp only [bitToF2_xor, bitToF2_and]
  ring_nf
  simp [pow_two, bitToF2_sq] ; ring_nf; simp [F2_mul_two]

theorem pcCombine_assoc (e f g : PCExponent) :
    pcCombine (pcCombine e f) g = pcCombine e (pcCombine f g) := by
  funext i
  fin_cases i
  · exact pcCombine_assoc_zero e f g
  · exact pcCombine_assoc_one e f g
  · exact pcCombine_assoc_two e f g
  · exact pcCombine_assoc_three e f g
  · exact pcCombine_assoc_four e f g
  · exact pcCombine_assoc_five e f g

end InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
