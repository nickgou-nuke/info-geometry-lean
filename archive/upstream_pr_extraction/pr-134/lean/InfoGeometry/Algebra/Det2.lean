import Mathlib.Tactic
set_option autoImplicit false

namespace Audit

variable {R : Type*} [CommRing R]

def det2 (a b c d : R) : R := a * d - b * c

def tr2 (a b c d : R) : R := a + d

theorem det2_identity : det2 (1 : R) 0 0 1 = 1 := by unfold det2; ring
theorem det2_duplicate_rows_zero (a b : R) : det2 a b a b = 0 := by unfold det2; ring
theorem det2_duplicate_cols_zero (a b : R) : det2 a a b b = 0 := by unfold det2; ring
theorem det2_swap_rows (a b c d : R) : det2 c d a b = - det2 a b c d := by unfold det2; ring
theorem det2_swap_cols (a b c d : R) : det2 b a d c = - det2 a b c d := by unfold det2; ring
theorem det2_row1_add (a b a' b' c d : R) : det2 (a + a') (b + b') c d = det2 a b c d + det2 a' b' c d := by unfold det2; ring
theorem det2_row2_add (a b c d c' d' : R) : det2 a b (c + c') (d + d') = det2 a b c d + det2 a b c' d' := by unfold det2; ring
theorem det2_col1_add (a c a' c' b d : R) : det2 (a + a') b (c + c') d = det2 a b c d + det2 a' b c' d := by unfold det2; ring
theorem det2_col2_add (a c b d b' d' : R) : det2 a (b + b') c (d + d') = det2 a b c d + det2 a b' c d' := by unfold det2; ring
theorem det2_row1_smul (r a b c d : R) : det2 (r * a) (r * b) c d = r * det2 a b c d := by unfold det2; ring
theorem det2_row2_smul (r a b c d : R) : det2 a b (r * c) (r * d) = r * det2 a b c d := by unfold det2; ring
theorem det2_col1_smul (r a b c d : R) : det2 (r * a) b (r * c) d = r * det2 a b c d := by unfold det2; ring
theorem det2_col2_smul (r a b c d : R) : det2 a (r * b) c (r * d) = r * det2 a b c d := by unfold det2; ring
theorem det2_upper_triangular (a b d : R) : det2 a b 0 d = a * d := by unfold det2; ring
theorem det2_lower_triangular (a c d : R) : det2 a 0 c d = a * d := by unfold det2; ring
theorem det2_mul (a b c d e f g h : R) :
    det2 (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h) = det2 a b c d * det2 e f g h := by
  unfold det2; ring

/-- Determinant of the sum identity for 2×2 matrices:
det(A+B) = det(A) + det(B) + tr(A)·tr(B) − tr(AB). -/
theorem det2_sum (a b c d e f g h : R) :
    det2 (a + e) (b + f) (c + g) (d + h) = det2 a b c d + det2 e f g h + tr2 a b c d * tr2 e f g h
    - tr2 (a*e + b*g) (a*f + b*h) (c*e + d*g) (c*f + d*h) := by
  unfold det2 tr2; ring

/-- Infinitesimal determinant: det(I + A) = 1 + tr(A) + det(A).
This is the 2×2 case of the expansion det(I + εA) = 1 + ε·tr(A) + O(ε²)
evaluated at ε = 1. -/
theorem det2_deriv_at_one (a b c d : R) :
    det2 (1 + a) b c (1 + d) = det2 (1 : R) 0 0 1 + tr2 a b c d + det2 a b c d := by
  unfold det2 tr2; ring

/--
Krein-space connection: For the (1,1) signature metric J = diag(1, -1),
det(J) = -1, matching the indefinite signed volume.
-/
theorem det2_krein_matrix : det2 (1 : ℝ) 0 0 (-1 : ℝ) = -1 := by
  unfold det2; ring

end Audit
