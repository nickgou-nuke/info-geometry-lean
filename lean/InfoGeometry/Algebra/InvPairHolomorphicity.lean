import Mathlib

open Matrix

noncomputable section

namespace InfoGeometry.Algebra.InvPairHolomorphicity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Inv-Pair Preservation: Conjugation preserves inverse structure -/
theorem inv_pair_conj (u x : Matrix n n R) [Invertible u] [Invertible x] :
    (⅟u * ⅟x * u) * (⅟u * x * u) = 1 ∧ (⅟u * x * u) * (⅟u * ⅟x * u) = 1 := by
  constructor
  · calc
      (⅟u * ⅟x * u) * (⅟u * x * u) = ⅟u * ⅟x * (u * ⅟u) * x * u := by simp [Matrix.mul_assoc]
      _ = ⅟u * ⅟x * 1 * x * u := by rw [mul_invOf_self]
      _ = ⅟u * (⅟x * x) * u := by simp [Matrix.mul_assoc]
      _ = ⅟u * 1 * u := by rw [invOf_mul_self]
      _ = ⅟u * u := by simp
      _ = 1 := by rw [invOf_mul_self]
  · calc
      (⅟u * x * u) * (⅟u * ⅟x * u) = ⅟u * x * (u * ⅟u) * ⅟x * u := by simp [Matrix.mul_assoc]
      _ = ⅟u * x * 1 * ⅟x * u := by rw [mul_invOf_self]
      _ = ⅟u * (x * ⅟x) * u := by simp [Matrix.mul_assoc]
      _ = ⅟u * 1 * u := by rw [mul_invOf_self]
      _ = ⅟u * u := by simp
      _ = 1 := by rw [invOf_mul_self]

/-- Triple-product Inv-Pair Preservation -/
theorem inv_pair_conj_three (u v x : Matrix n n R) [Invertible u] [Invertible v] [Invertible x] :
    (⅟v * ⅟u * ⅟x * u * v) * (⅟v * ⅟u * x * u * v) = 1 := by
  calc
    (⅟v * ⅟u * ⅟x * u * v) * (⅟v * ⅟u * x * u * v) = ⅟v * ⅟u * ⅟x * u * (v * ⅟v) * ⅟u * x * u * v := by simp [Matrix.mul_assoc]
    _ = ⅟v * ⅟u * ⅟x * u * 1 * ⅟u * x * u * v := by rw [mul_invOf_self]
    _ = ⅟v * ⅟u * ⅟x * (u * ⅟u) * x * u * v := by simp [Matrix.mul_assoc]
    _ = ⅟v * ⅟u * ⅟x * 1 * x * u * v := by rw [mul_invOf_self]
    _ = ⅟v * ⅟u * (⅟x * x) * u * v := by simp [Matrix.mul_assoc]
    _ = ⅟v * ⅟u * 1 * u * v := by rw [invOf_mul_self]
    _ = ⅟v * (⅟u * u) * v := by simp [Matrix.mul_assoc]
    _ = ⅟v * 1 * v := by rw [invOf_mul_self]
    _ = ⅟v * v := by simp
    _ = 1 := by rw [invOf_mul_self]

/-- Certified Inv-Pair Preservation Packet -/
structure InvPairPreservationPacket (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] where
  conj_left : ∀ (u x : Matrix n n R) [Invertible u] [Invertible x],
    (⅟u * ⅟x * u) * (⅟u * x * u) = 1
  conj_right : ∀ (u x : Matrix n n R) [Invertible u] [Invertible x],
    (⅟u * x * u) * (⅟u * ⅟x * u) = 1

theorem inv_pair_preservation_packet_exists : Nonempty (InvPairPreservationPacket n R) :=
  ⟨⟨fun u x => (inv_pair_conj u x).1, fun u x => (inv_pair_conj u x).2⟩⟩

end InfoGeometry.Algebra.InvPairHolomorphicity