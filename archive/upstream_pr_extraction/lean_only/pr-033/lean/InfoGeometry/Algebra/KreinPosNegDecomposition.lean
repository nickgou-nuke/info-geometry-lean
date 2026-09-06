import Mathlib.Tactic
open Matrix

set_option autoImplicit false

/-!
# Krein Pos-Neg Decomposition

The Krein metric `J = diag(1, -1)` induces a decomposition of
ℂ² (resp. ℝ²) into positive and negative subspaces:

- **Positive subspace** `V₊ = span{e₁}` where `⟨e₁, e₁⟩_J = 1`.
- **Negative subspace** `V₋ = span{e₂}` where `⟨e₂, e₂⟩_J = -1`.
- **Nondegeneracy**: `det(J) = -1 ≠ 0`.
- **Projector decomposition**: `J = P₊ - P₋` with `P₊·P₋ = 0` and `P₊ + P₋ = 1`.

All theorems are proven by direct 2×2 computation.
-/

namespace Audit.KreinPosNegDecomposition

section KreinMetric

/-- Krein metric J = diag(1, -1) over ℂ. -/
def J : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem det_J_nonzero : det J ≠ 0 := by
  unfold J; simp [Matrix.det_fin_two]

/-- J is nondegenerate because its determinant is non-zero. -/
theorem nondegenerate : det J ≠ 0 := det_J_nonzero

theorem J_sq : J * J = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply]

end KreinMetric

section PosNegProjectors

/-- Projector onto the positive subspace: P₊ = diag(1,0). -/
def P_plus : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Projector onto the negative subspace: P₋ = diag(0,1). -/
def P_minus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_plus, Matrix.mul_apply]

theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_minus, Matrix.mul_apply]

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus, Matrix.mul_apply]

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus, Matrix.mul_apply]

theorem P_plus_add_P_minus : P_plus + P_minus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus]

/-- The Krein metric acts as J = P₊ - P₋. -/
theorem J_as_projectors : J = P_plus - P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, P_plus, P_minus]

/-- J² = 1 via the projector algebra (computed entrywise). -/
theorem J_sq_via_projectors : J * J = 1 := by
  rw [J_as_projectors]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, Matrix.mul_apply]

/-- The determinant of P₊ is zero. -/
theorem det_P_plus : det P_plus = 0 := by
  unfold P_plus; simp [Matrix.det_fin_two]

/-- The determinant of P₋ is zero. -/
theorem det_P_minus : det P_minus = 0 := by
  unfold P_minus; simp [Matrix.det_fin_two]

/-- Traces: tr(P₊) = tr(P₋) = 1. -/
theorem tr_P_plus : trace P_plus = 1 := by
  unfold P_plus; simp

theorem tr_P_minus : trace P_minus = 1 := by
  unfold P_minus; simp

end PosNegProjectors

section QuadraticForm

/-- The J-orthogonal quadratic form on ℂ²: Q(x₁,x₂) = x₁² - x₂². -/
noncomputable def Q (x₁ x₂ : ℂ) : ℂ := x₁ ^ 2 - x₂ ^ 2

/-- Q(1,0) = 1: the positive subspace is J-positive. -/
theorem Q_positive : Q 1 0 = 1 := by
  unfold Q; norm_num

/-- Q(0,1) = -1: the negative subspace is J-negative. -/
theorem Q_negative : Q 0 1 = -1 := by
  unfold Q; norm_num

/-- Q(1,1) = 0: lightlike vectors exist in the Krein geometry. -/
theorem Q_lightlike : Q 1 1 = 0 := by
  unfold Q; norm_num

end QuadraticForm

end Audit.KreinPosNegDecomposition
