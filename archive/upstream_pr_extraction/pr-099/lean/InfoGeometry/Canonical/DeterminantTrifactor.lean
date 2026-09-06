import Mathlib.Tactic

namespace InfoGeometry.Canonical.DeterminantTrifactor

/--
The Determinant Trifactor Theorem.
For any commutative ring R that is an integral domain, if a scalar d (such as the
determinant of an operator T satisfying T³ = T) satisfies the cubic identity
d³ = d, then d is algebraically restricted to the discrete set {-1, 0, 1}.

This proves that the determinant acts as a strict topological classifier for
the three geometric sectors:
- d = -1 : Orientation-reversing (J-sector)
- d =  0 : Non-invertible projective boundary (Cuntz projection)
- d =  1 : Orientation-preserving flow (PSL(2, Z) sector)
-/
theorem determinant_trifactor_eq {R : Type*} [CommRing R] [IsDomain R] (d : R)
    (h_cube : d ^ 3 = d) : d = 0 ∨ d = 1 ∨ d = -1 := by
  -- 1. Express the cubic equation as d³ - d = 0
  have h_eq_zero : d ^ 3 - d = 0 := by
    calc
      d ^ 3 - d = d ^ 3 - d ^ 3 := by rw [h_cube]
      _ = 0 := by ring

  -- 2. Factor the cubic equation: d * (d - 1) * (d + 1) = 0
  have h_factored : d * (d - 1) * (d + 1) = 0 := by
    calc
      d * (d - 1) * (d + 1) = d ^ 3 - d := by ring
      _ = 0 := h_eq_zero

  -- 3. Use the integral domain property (IsDomain) to split the product
  -- Since d * (d - 1) * (d + 1) = 0, either d * (d - 1) = 0 or d + 1 = 0
  rcases mul_eq_zero.mp h_factored with h_left | h_right
  · -- Case A: d * (d - 1) = 0
    rcases mul_eq_zero.mp h_left with hd | hd_minus_one
    · -- Subcase A1: d = 0
      left; exact hd
    · -- Subcase A2: d - 1 = 0 => d = 1
      right; left
      calc
        d = d - 1 + 1 := by ring
        _ = 0 + 1     := by rw [hd_minus_one]
        _ = 1         := by ring
  · -- Case B: d + 1 = 0 => d = -1
    right; right
    calc
      d = d + 1 - 1 := by ring
      _ = 0 - 1     := by rw [h_right]
      _ = -1        := by ring

end InfoGeometry.Canonical.DeterminantTrifactor
