import Mathlib.Tactic

/-!
# Determinant Trifactor — Lean 4

For any commutative ring R that is an integral domain:
  d³ = d  ⇒  d ∈ {-1, 0, 1}

This classifies the determinant of any operator T with T³ = T
into three topological sectors:
  det = -1  →  orientation-reversing (J-sector)
  det =  0  →  non-invertible boundary (Cuntz projection)
  det = +1  →  orientation-preserving flow (PSL(2,ℤ))
-/

noncomputable section

namespace DeterminantTrifactor

theorem determinant_trifactor_eq {R : Type*} [CommRing R] [IsDomain R] (d : R)
    (h_cube : d ^ 3 = d) : d = 0 ∨ d = 1 ∨ d = -1 := by
  -- 1. d³ - d = 0
  have h_eq_zero : d ^ 3 - d = 0 := by
    calc
      d ^ 3 - d = d - d := by rw [h_cube]
      _ = 0 := by ring

  -- 2. Factor: d(d-1)(d+1) = 0
  have h_factored : d * (d - 1) * (d + 1) = 0 := by
    calc
      d * (d - 1) * (d + 1) = d ^ 3 - d := by ring
      _ = 0 := h_eq_zero

  -- 3. Integral domain: product = 0 ⇒ one factor = 0
  rcases mul_eq_zero.mp h_factored with h_first | h_right
  · -- Case A: d * (d - 1) = 0
    rcases mul_eq_zero.mp h_first with hd | hd_minus_one
    · -- d = 0
      left; exact hd
    · -- d - 1 = 0 ⇒ d = 1
      right; left
      calc
        d = d - 1 + 1 := by ring
        _ = 0 + 1     := by rw [hd_minus_one]
        _ = 1         := by ring
  · -- Case B: d + 1 = 0 ⇒ d = -1
    right; right
    calc
      d = d + 1 - 1 := by ring
      _ = 0 - 1     := by rw [h_right]
      _ = -1        := by ring

end DeterminantTrifactor
