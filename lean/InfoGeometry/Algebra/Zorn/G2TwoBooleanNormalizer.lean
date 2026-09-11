import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

lemma bitToF2_xor (a b : Bool) :
    bitToF2 (a ^^ b) = bitToF2 a + bitToF2 b := by
  rw [← bitToF2_add]

lemma bitToF2_and (a b : Bool) :
    bitToF2 (a && b) = bitToF2 a * bitToF2 b := by
  cases a <;> cases b <;> simp [bitToF2]

lemma bitToF2_eq_iff (a b : Bool) :
    bitToF2 a = bitToF2 b ↔ a = b := by
  constructor
  · intro h
    simpa only [f2ToBit_bitToF2] using congrArg f2ToBit h
  · intro h
    simp only [h]

lemma bitToF2_sq (a : Bool) : bitToF2 a * bitToF2 a = bitToF2 a := by
  cases a <;> simp [bitToF2]

lemma bitToF2_pow (a : Bool) (n : ℕ) :
    bitToF2 a ^ n = if n = 0 then 1 else bitToF2 a := by
  cases a
  · cases n <;> simp [bitToF2]
  · cases n with
    | zero => simp [bitToF2]
    | succ n =>
      simp only [bitToF2, ite_true, one_pow]
      cases n <;> simp

lemma bitToF2_map_ite {α : Type*} (p : Bool) (x y : α)
    (q : α → Bool) :
    bitToF2 (q (if p then x else y)) =
      bitToF2 p * bitToF2 (q x) +
        (1 + bitToF2 p) * bitToF2 (q y) := by
  cases p <;> simp [bitToF2]

lemma bitToF2_ite (p x y : Bool) :
    bitToF2 (if p then x else y) =
      bitToF2 p * bitToF2 x + (1 + bitToF2 p) * bitToF2 y := by
  exact bitToF2_map_ite p x y id

end InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
