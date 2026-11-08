import InfoGeometry.OperatorAlgebra.PeirceSpine.ParityCoboundary
import Mathlib.Algebra.Ring.Invertible

/-! # Exactness of the additive parity difference when two is invertible

The witness for a trace-zero operator Y is `(⅟2)*Y`. The ambient ring
remains arbitrary and noncommutative. This is an additive exactness result,
not the multiplicative Hilbert 90 theorem.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [Invertible (2 : B)]

theorem ringEquiv_map_half (g : B ≃+* B) : g (⅟(2 : B)) = ⅟(2 : B) := by
  have h : (2 : B) * g (⅟(2 : B)) = 1 := by
    calc
      (2 : B) * g (⅟(2 : B)) = g (2 * ⅟(2 : B)) := by rw [map_mul, map_ofNat]
      _ = 1 := by rw [mul_invOf_self, map_one]
  exact (invOf_eq_right_inv h).symm

/-- Explicit primitive of any trace-zero operator. -/
theorem automorphismDifference_half (g : B ≃+* B) {Y : B}
    (hY : Y + g Y = 0) :
    automorphismDifference g ((⅟(2 : B)) * Y) = Y := by
  have hg : g Y = -Y := eq_neg_of_add_eq_zero_right hY
  change (⅟(2 : B)) * Y - g ((⅟(2 : B)) * Y) = Y
  rw [map_mul, ringEquiv_map_half, hg, mul_neg, sub_neg_eq_add,
    ← add_mul, invOf_two_add_invOf_two, one_mul]

/-- The range of one minus an involution equals the kernel of its trace. -/
theorem trace_zero_iff_exists_automorphismDifference (g : B ≃+* B)
    (hg : Function.Involutive g) (Y : B) :
    Y + g Y = 0 ↔ ∃ X : B, automorphismDifference g X = Y := by
  constructor
  · intro hY
    exact ⟨(⅟(2 : B)) * Y, automorphismDifference_half g hY⟩
  · rintro ⟨X, rfl⟩
    change (X - g X) + g (X - g X) = 0
    rw [map_sub, hg X]
    abel

theorem parity_trace_zero_iff_exists_difference {P : B} (hP : P * P = P) (Y : B) :
    Y + parityConj P Y = 0 ↔ ∃ X : B, X - parityConj P X = Y :=
  trace_zero_iff_exists_automorphismDifference (parityConjRingEquiv hP)
    (fun X => (parityConj_involutive_ring_action hP X 1).1) Y

end InfoGeometry.OperatorAlgebra.PeirceSpine
