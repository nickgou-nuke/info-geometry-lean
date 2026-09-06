import Mathlib.Tactic
import InfoGeometry.Canonical.ErlangenInductiveClosure
import InfoGeometry.Canonical.ErlangenColimitResolution

/-!
# Zorn Matrix Algebra Supergraded Inductive Closure Bridge

This module instantiates the abstract `SupergradedClosureAt` invariant packet
and the `CausalPreorder` class for the native Mathlib 2x2 matrix algebra over the real numbers.
-/

open InfoGeometry.Canonical.ErlangenInductiveClosure
open InfoGeometry.Canonical.ErlangenColimitResolution

namespace InfoGeometry.Automath.Generated

/-- Odd elements are in the off-diagonal isotropic matrix spaces. -/
def matrix_is_odd (X : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∃ u : ℝ, X = ![![0, u], ![0, 0]]) ∨ (∃ v : ℝ, X = ![![0, 0], ![v, 0]])

/-- Even elements are the diagonal matrices. -/
def matrix_is_even (X : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ a b : ℝ, X = ![![a, 0], ![0, b]]

/-- Central elements are the scalar multiples of the identity matrix. -/
def matrix_is_central (X : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ a : ℝ, X = ![![a, 0], ![0, a]]

lemma matrix_odd_nilpotency_proof (X : Matrix (Fin 2) (Fin 2) ℝ) (h : matrix_is_odd X) : X * X = 0 := by
  rcases h with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma matrix_odd_odd_closure_proof (X Y : Matrix (Fin 2) (Fin 2) ℝ) (hx : matrix_is_odd X) (hy : matrix_is_odd Y) :
    matrix_is_even (X * Y + Y * X) := by
  rcases hx with ⟨u, rfl⟩ | ⟨v, rfl⟩ <;> rcases hy with ⟨s, rfl⟩ | ⟨t, rfl⟩
  · -- X = upper, Y = upper
    use 0, 0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · -- X = upper, Y = lower
    use u * t, t * u
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · -- X = lower, Y = upper
    use s * v, v * s
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · -- X = lower, Y = lower
    use 0, 0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma matrix_central_lane_proof (C X : Matrix (Fin 2) (Fin 2) ℝ) (hc : matrix_is_central C) : C * X = X * C := by
  rcases hc with ⟨a, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Projector E11 is even and idempotent. -/
lemma matrix_projector_identity_proof : ∃ P : Matrix (Fin 2) (Fin 2) ℝ, matrix_is_even P ∧ P * P = P := by
  use ![![1, 0], ![0, 0]]
  constructor
  · use 1, 0
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Instantiates the `SupergradedClosureAt` structure for `Matrix (Fin 2) (Fin 2) ℝ`. -/
def matrix_supergraded_closure : SupergradedClosureAt (Matrix (Fin 2) (Fin 2) ℝ) where
  is_odd := matrix_is_odd
  is_even := matrix_is_even
  is_central := matrix_is_central
  odd_nilpotency := matrix_odd_nilpotency_proof
  odd_odd_closure := matrix_odd_odd_closure_proof
  central_lane := matrix_central_lane_proof
  projector_identity := matrix_projector_identity_proof

/-- Pointwise preorder on 2x2 matrices over real numbers. -/
instance : Preorder (Matrix (Fin 2) (Fin 2) ℝ) where
  le X Y := ∀ i j, X i j ≤ Y i j
  le_refl X i j := le_refl _
  le_trans X Y Z h1 h2 i j := le_trans (h1 i j) (h2 i j)

/-- Instantiates the `CausalPreorder` class for `Matrix (Fin 2) (Fin 2) ℝ`. -/
instance : CausalPreorder (Matrix (Fin 2) (Fin 2) ℝ) where
  toPreorder := inferInstance
  add_le_add_left X Y h C i j := by
    change C i j + X i j ≤ C i j + Y i j
    rw [add_comm (C i j) (X i j), add_comm (C i j) (Y i j)]
    exact add_le_add_left (h i j) (C i j)

end InfoGeometry.Automath.Generated
