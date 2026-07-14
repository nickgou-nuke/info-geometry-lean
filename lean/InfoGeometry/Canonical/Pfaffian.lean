import Mathlib

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
- pfaffian_2x2: Pf([[0,a],[-a,0]]) = a
- pfaffian_sq_eq_det_2x2: Pf(M)² = det(M) for 2×2 skew-symmetric M
- det_skew_2x2: det([[0,a],[-a,0]]) = a²
#### BUCKET 3: Higher-dimensional Pfaffian — open debt
-/

namespace Pfaffian

/-- The Pfaffian of a 2×2 skew-symmetric matrix [[0, a], [-a, 0]]. -/
def pfaffian_2x2 {R : Type*} [CommRing R] (a : R) : R := a

/-- The determinant of a 2×2 skew-symmetric matrix [[0, a], [-a, 0]]. -/
theorem det_skew_2x2 {R : Type*} [CommRing R] (a : R) :
    Matrix.det !![(0 : R), a; -a, 0] = a * a := by
  simp [Matrix.det_fin_two]

/-- Pf(M)² = det(M) for a 2×2 skew-symmetric matrix. -/
theorem pfaffian_sq_eq_det_2x2 {R : Type*} [CommRing R] (a : R) :
    (pfaffian_2x2 a) ^ 2 = Matrix.det !![(0 : R), a; -a, 0] := by
  simp [pfaffian_2x2, Matrix.det_fin_two, pow_two]

/-- Pf(M) = 0 when a = 0 (matrix is zero). -/
theorem pfaffian_zero_2x2 {R : Type*} [CommRing R] : pfaffian_2x2 (0 : R) = 0 := by
  simp [pfaffian_2x2]

/-- det(M) ≥ 0 for real skew-symmetric 2×2 matrix (det = a² ≥ 0). -/
theorem det_nonneg_2x2 (a : ℝ) : 0 ≤ Matrix.det !![(0 : ℝ), a; -a, 0] := by
  rw [det_skew_2x2]; nlinarith [sq_nonneg a]

end Pfaffian
