import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Invariant Fisher–Rao Riemannian Geometry on the Symmetric Matrix Cone P_n ≅ GL(n, ℝ)/O(n)

This module formalizes:
1. The congruence action of the General Linear Group GL(n, ℝ) on symmetric matrices:
     g • S = g * S * gᵀ
2. The isotropy stabilizer of the identity matrix I_n:
     Stab_{GL(n)}(I_n) = O(n)  (i.e., g * I * gᵀ = I ↔ g * gᵀ = I)
3. The Cartan–Fisher–Rao Riemannian metric on the tangent space of symmetric matrices:
     g_S(X, Y) = (1/2) * Tr(S⁻¹ * X * S⁻¹ * Y)
4. Strict GL(n, ℝ)-isometry invariance:
     g_{A * S * Aᵀ}(A * X * Aᵀ, A * Y * Aᵀ) = g_S(X, Y)
   proven natively with zero `sorry`s using the cyclic property of the matrix trace.
5. Strict metric positivity and non-degeneracy at the origin:
     g_I(X, X) = (1/2) * ∑_{i, j} X_{i, j}² ≥ 0
     g_I(X, X) = 0 ↔ X = 0  (for symmetric X).

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Architecture.MatrixSymmetricCone

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℝ

/-- The congruence action of a matrix A on a state S: A • S = A * S * Aᵀ. -/
def congruenceAction (A : Mat) (S : Mat) : Mat :=
  A * S * Aᵀ

@[simp]
theorem congruenceAction_apply (A S : Mat) :
    congruenceAction A S = A * S * Aᵀ := rfl

/-- Congruence action preserves matrix transpose / symmetry. -/
theorem congruenceAction_transpose (A S : Mat) (hS : Sᵀ = S) :
    (congruenceAction A S)ᵀ = congruenceAction A S := by
  dsimp [congruenceAction]
  rw [transpose_mul, transpose_mul, transpose_transpose, hS, mul_assoc]

/-- THEOREM 1: The isotropy stabilizer of I_n under congruence is the Orthogonal Group O(n). -/
theorem stabilizer_identity_eq_orthogonal (A : Mat) :
    congruenceAction A 1 = 1 ↔ A * Aᵀ = 1 := by
  dsimp [congruenceAction]
  rw [mul_one]

/-- The Fisher–Rao metric tensor at point S with inverse S_inv: g_S(X, Y) = (1/2) * Tr(S⁻¹ * X * S⁻¹ * Y). -/
def fisherRaoMetric (S_inv : Mat) (X Y : Mat) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (S_inv * X * S_inv * Y)

/-- THEOREM 2 (Symmetry of the Fisher–Rao metric): g_S(X, Y) = g_S(Y, X). -/
theorem fisherRaoMetric_symm (S_inv : Mat) (X Y : Mat) :
    fisherRaoMetric S_inv X Y = fisherRaoMetric S_inv Y X := by
  dsimp [fisherRaoMetric]
  congr 1
  have h := Matrix.trace_mul_comm (S_inv * X) (S_inv * Y)
  simp only [mul_assoc] at h ⊢
  exact h

/-- 
  THEOREM 3 (Exact GL(n, ℝ)-Invariance):
  Under the congruence transformation S ↦ A * S * Aᵀ, the inverse transforms as:
    (A * S * Aᵀ)⁻¹ = (Aᵀ)⁻¹ * S⁻¹ * A⁻¹
  and the Fisher–Rao metric is strictly invariant:
    g_{A * S * Aᵀ}(A * X * Aᵀ, A * Y * Aᵀ) = g_S(X, Y).
-/
theorem fisherRaoMetric_congruence_invariant
    (A S_inv : Mat) (A_inv : Mat)
    (hA_left : A_inv * A = 1) (_hA_right : A * A_inv = 1)
    (X Y : Mat) :
    fisherRaoMetric (A_invᵀ * S_inv * A_inv) (congruenceAction A X) (congruenceAction A Y) =
      fisherRaoMetric S_inv X Y := by
  dsimp [fisherRaoMetric, congruenceAction]
  congr 1
  have h_AT_AinvT : Aᵀ * A_invᵀ = (1 : Mat) := by
    rw [← transpose_mul, hA_left, transpose_one]
  have h_inner :
      (A_invᵀ * S_inv * A_inv) * (A * X * Aᵀ) * (A_invᵀ * S_inv * A_inv) * (A * Y * Aᵀ)
      = A_invᵀ * (S_inv * X * S_inv * Y) * Aᵀ := by
    calc
      (A_invᵀ * S_inv * A_inv) * (A * X * Aᵀ) * (A_invᵀ * S_inv * A_inv) * (A * Y * Aᵀ)
        = A_invᵀ * S_inv * (A_inv * A) * X * (Aᵀ * A_invᵀ) * S_inv * (A_inv * A) * Y * Aᵀ := by
          simp only [mul_assoc]
      _ = A_invᵀ * S_inv * 1 * X * 1 * S_inv * 1 * Y * Aᵀ := by
          rw [hA_left, h_AT_AinvT]
      _ = A_invᵀ * (S_inv * X * S_inv * Y) * Aᵀ := by
          simp only [mul_one, mul_assoc]
  rw [h_inner]
  have h_comm := Matrix.trace_mul_comm (A_invᵀ * (S_inv * X * S_inv * Y)) Aᵀ
  rw [h_comm]
  have h_id : Aᵀ * (A_invᵀ * (S_inv * X * S_inv * Y)) = S_inv * X * S_inv * Y := by
    rw [← mul_assoc, h_AT_AinvT, one_mul]
  rw [h_id]

/-- At the identity S = I, the Fisher–Rao metric simplifies to (1/2) * Tr(X * Y). -/
theorem fisherRaoMetric_at_identity (X Y : Mat) :
    fisherRaoMetric 1 X Y = (1 / 2 : ℝ) * Matrix.trace (X * Y) := by
  dsimp [fisherRaoMetric]
  simp only [one_mul, mul_one]

/-- Matrix trace of X * X for symmetric X is the sum of squared elements. -/
theorem trace_mul_self_eq_sum_sq (X : Mat) (hX : Xᵀ = X) :
    Matrix.trace (X * X) = ∑ i, ∑ j, (X i j) ^ 2 := by
  dsimp [Matrix.trace, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hX_ij : X j i = X i j := by
    rw [← Matrix.transpose_apply X i j, hX]
  rw [hX_ij, sq]

/-- THEOREM 4: Strict non-negativity of the Fisher–Rao metric at the basepoint. -/
theorem fisherRaoMetric_nonneg_at_identity (X : Mat) (hX : Xᵀ = X) :
    0 ≤ fisherRaoMetric 1 X X := by
  rw [fisherRaoMetric_at_identity, trace_mul_self_eq_sum_sq X hX]
  have h_sum_nonneg : 0 ≤ ∑ i, ∑ j, (X i j) ^ 2 := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact sq_nonneg (X i j)
  exact mul_nonneg (by linarith) h_sum_nonneg

/-- THEOREM 5: Non-degeneracy of the Fisher–Rao metric on symmetric matrices. -/
theorem fisherRaoMetric_zero_iff_at_identity (X : Mat) (hX : Xᵀ = X) :
    fisherRaoMetric 1 X X = 0 ↔ X = 0 := by
  rw [fisherRaoMetric_at_identity, trace_mul_self_eq_sum_sq X hX]
  have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
  constructor
  · intro h
    have h_sum : (∑ i, ∑ j, (X i j) ^ 2) = 0 := by
      have := mul_eq_zero.mp h
      cases this with
      | inl h1 => linarith
      | inr h2 => exact h2
    have h_sq_zero (i : n) (j : n) : X i j = 0 := by
      have h_all_rows_nonneg (k : n) (_hk : k ∈ Finset.univ) : 0 ≤ ∑ j, (X k j) ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg (X k j))
      have h_row_zero := (Finset.sum_eq_zero_iff_of_nonneg h_all_rows_nonneg).mp h_sum i (Finset.mem_univ i)
      have h_terms_nonneg (l : n) (_hl : l ∈ Finset.univ) : 0 ≤ (X i l) ^ 2 := sq_nonneg (X i l)
      have h_elem_zero := (Finset.sum_eq_zero_iff_of_nonneg h_terms_nonneg).mp h_row_zero j (Finset.mem_univ j)
      exact sq_eq_zero_iff.mp h_elem_zero
    ext i j
    exact h_sq_zero i j
  · intro h
    subst h
    simp

end InfoGeometry.Architecture.MatrixSymmetricCone

end noncomputable section
