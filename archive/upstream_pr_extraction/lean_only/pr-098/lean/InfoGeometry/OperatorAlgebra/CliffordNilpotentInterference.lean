import Mathlib.Tactic

/-!
# Nilpotent interference of elliptic and split generators

This owner records only the local associative-algebra identity.  It does not
identify the generators with a KAN, transport, or learning dynamics.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordNilpotentInterference

variable {A : Type*} [Ring A]

/-- Opposite quadratic signs and anticommutation force a square-zero sum. -/
theorem add_sq_zero_of_opposite_squares
    (B K : A)
    (hB : B * B = -(1 : A))
    (hK : K * K = 1)
    (hBK : B * K = -(K * B)) :
    (B + K) * (B + K) = 0 := by
  simp only [add_mul, mul_add]
  rw [hB, hK, hBK]
  abel

/-- The opposite-sign combination is square-zero under the same hypotheses. -/
theorem sub_sq_zero_of_opposite_squares
    (B K : A)
    (hB : B * B = -(1 : A))
    (hK : K * K = 1)
    (hBK : B * K = -(K * B)) :
    (B - K) * (B - K) = 0 := by
  simp only [sub_mul, mul_sub]
  rw [hB, hK, hBK]
  abel

end InfoGeometry.OperatorAlgebra.CliffordNilpotentInterference
