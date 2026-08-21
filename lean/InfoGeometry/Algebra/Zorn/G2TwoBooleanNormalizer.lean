import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

namespace InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

lemma bitToF2_xor (a b : Bool) :
    bitToF2 (a ^^ b) = bitToF2 a + bitToF2 b := by
  rw [← bitToF2_add]

lemma bitToF2_and (a b : Bool) :
    bitToF2 (a && b) = bitToF2 a * bitToF2 b := by
  cases a <;> cases b <;> rfl

lemma bitToF2_eq_iff (a b : Bool) :
    bitToF2 a = bitToF2 b ↔ a = b := by
  constructor
  · intro h
    simpa only [f2ToBit_bitToF2] using congrArg f2ToBit h
  · intro h
    simpa [h]

end InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
