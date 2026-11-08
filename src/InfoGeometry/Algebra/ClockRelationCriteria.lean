import InfoGeometry.Algebra.CuntzClockObstructions

/-!
# Exact commutation and anticommutation criteria for a Weyl pair

Contract: X and Z belong to the original, possibly noncommutative complex
algebra. Under ZX=qXZ, commutation and anticommutation are characterized
including the degenerate product-zero case. No invertibility is required.
-/
namespace InfoGeometry.Algebra.CuntzClockObstructions

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem clock_commutes_iff (X Z : A) (q : ℂ)
    (h : Z * X = q • (X * Z)) :
    Commute X Z ↔ q = 1 ∨ X * Z = 0 := by
  change X * Z = Z * X ↔ _
  rw [← sub_eq_zero, clock_commutator X Z q h, smul_eq_zero]
  simp only [sub_eq_zero]
  exact or_congr eq_comm Iff.rfl

theorem clock_anticommutes_iff (X Z : A) (q : ℂ)
    (h : Z * X = q • (X * Z)) :
    X * Z + Z * X = 0 ↔ q = -1 ∨ X * Z = 0 := by
  rw [clock_anticommutator X Z q h, smul_eq_zero]
  simp only [add_comm (1 : ℂ) q, add_eq_zero_iff_eq_neg]

end InfoGeometry.Algebra.CuntzClockObstructions
