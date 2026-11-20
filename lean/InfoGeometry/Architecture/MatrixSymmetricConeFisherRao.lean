/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import InfoGeometry.OperatorAlgebra.RealMatrixSplit
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
    (hA_left : A_inv * A = 1)
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
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) h_sum_nonneg

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

open InfoGeometry.OperatorAlgebra.RealMatrixSplit

/-- The linear term of the covariance congruence action in generator `A`. -/
def congruenceTangent (S A : Mat) : Mat := A * S + S * Aᵀ

/-- An exact polynomial expansion identifies the congruence tangent. -/
theorem congruenceAction_affine_generator (S A : Mat) (t : ℝ) :
    congruenceAction (1 + t • A) S =
      S + t • congruenceTangent S A + t ^ 2 • congruenceAction A S := by
  simp only [congruenceAction, congruenceTangent, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_smul, add_mul, mul_add,
    one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    pow_two]
  abel

omit [DecidableEq n] in
/-- A symmetric covariance has a symmetric congruence tangent. -/
theorem congruenceTangent_transpose (S A : Mat) (hS : Sᵀ = S) :
    (congruenceTangent S A)ᵀ = congruenceTangent S A := by
  simp only [congruenceTangent, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, hS]
  abel

/-- The skew generator contributes a commutator, including at anisotropic
covariances. No commutation hypothesis discards that contribution. -/
theorem congruenceTangent_of_split (S G Ω A : Mat)
    (hG : Gᵀ = G) (hΩ : Ωᵀ = -Ω) (hA : G + Ω = A) :
    congruenceTangent S A =
      (G * S + S * G) + (Ω * S - S * Ω) := by
  rw [congruenceTangent, ← hA, Matrix.transpose_add, hG, hΩ]
  noncomm_ring

/-- Polarization retains the two ordered mixed contributions, combined using
the already established symmetry of the Fisher bilinear form. -/
theorem fisherRaoMetric_add_self (S_inv X Y : Mat) :
    fisherRaoMetric S_inv (X + Y) (X + Y) =
      fisherRaoMetric S_inv X X + 2 * fisherRaoMetric S_inv X Y +
        fisherRaoMetric S_inv Y Y := by
  have hsym := fisherRaoMetric_symm S_inv X Y
  simp only [fisherRaoMetric, mul_add, add_mul, Matrix.trace_add] at hsym ⊢
  simp only [← hsym, two_mul, add_assoc]

/-- The full matrix pullback contains a symmetric/skew mixed term. This is
the exact correction to an unconditional orthogonal three-sector split. -/
theorem fisherRaoMetric_congruenceTangent_split
    (S_inv S G Ω A : Mat)
    (hG : Gᵀ = G) (hΩ : Ωᵀ = -Ω) (hA : G + Ω = A) :
    fisherRaoMetric S_inv (congruenceTangent S A) (congruenceTangent S A) =
      fisherRaoMetric S_inv (G * S + S * G) (G * S + S * G) +
        2 * fisherRaoMetric S_inv (G * S + S * G) (Ω * S - S * Ω) +
        fisherRaoMetric S_inv (Ω * S - S * Ω) (Ω * S - S * Ω) := by
  rw [congruenceTangent_of_split S G Ω A hG hΩ hA]
  exact fisherRaoMetric_add_self S_inv _ _

/-- At the identity covariance, the skew generator is invisible to the
congruence tangent. -/
theorem congruenceTangent_identity (A : Mat) :
    congruenceTangent 1 A = (2 : ℝ) • (selfAdjointPart ℝ A : Mat) := by
  rw [congruenceTangent, selfAdjointPart_eq_half]
  simp only [mul_one, one_mul, smul_smul]
  norm_num

/-- A Gram covariance transports its tangent from the whitened generator.
The inverse is supplied explicitly; all matrix products retain their order. -/
theorem congruenceTangent_gram (G H A : Mat) (hGH : G * H = 1) :
    congruenceTangent (G * Gᵀ) A =
      congruenceAction G (H * A * G + (H * A * G)ᵀ) := by
  have hT : Hᵀ * Gᵀ = (1 : Mat) := by
    rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
  symm
  simp only [congruenceAction, Matrix.transpose_mul]
  calc
    G * (H * A * G + Gᵀ * (Aᵀ * Hᵀ)) * Gᵀ =
        (G * H) * A * (G * Gᵀ) + (G * Gᵀ) * Aᵀ * (Hᵀ * Gᵀ) := by
      noncomm_ring
    _ = congruenceTangent (G * Gᵀ) A := by
      rw [hGH, hT]
      simp [congruenceTangent]

/-- The existing Fisher congruence invariance gives the full, noncommuting
generator pullback at every invertible real Gram frame. -/
theorem fisherRaoMetric_congruenceTangent_gram
    (G H A : Mat) (hHG : H * G = 1) (hGH : G * H = 1) :
    fisherRaoMetric (Hᵀ * H)
        (congruenceTangent (G * Gᵀ) A) (congruenceTangent (G * Gᵀ) A) =
      fisherRaoMetric 1 (H * A * G + (H * A * G)ᵀ)
        (H * A * G + (H * A * G)ᵀ) := by
  rw [congruenceTangent_gram G H A hGH]
  simpa only [mul_one] using
    fisherRaoMetric_congruence_invariant G (1 : Mat) H hHG
      (H * A * G + (H * A * G)ᵀ) (H * A * G + (H * A * G)ᵀ)

/-- The pullback is twice the squared Frobenius norm of the native
self-adjoint part of the whitened generator. -/
theorem fisherRaoMetric_congruenceTangent_eq_sum_sq
    (G H A : Mat) (hHG : H * G = 1) (hGH : G * H = 1) :
    fisherRaoMetric (Hᵀ * H)
        (congruenceTangent (G * Gᵀ) A) (congruenceTangent (G * Gᵀ) A) =
      2 * ∑ i, ∑ j, ((selfAdjointPart ℝ (H * A * G) : Mat) i j) ^ 2 := by
  rw [fisherRaoMetric_congruenceTangent_gram G H A hHG hGH,
    fisherRaoMetric_at_identity]
  have hsym : (H * A * G + (H * A * G)ᵀ)ᵀ =
      H * A * G + (H * A * G)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  rw [trace_mul_self_eq_sum_sq _ hsym]
  simp only [Finset.mul_sum, selfAdjointPart_eq_half]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply, smul_eq_mul]
  let x : ℝ := (H * A * G + (H * A * G)ᵀ) i j
  have hreal : (1 / 2 : ℝ) * x ^ 2 = 2 * ((1 / 2 : ℝ) * x) ^ 2 := by
    ring
  exact hreal

/-- Positivity is obtained for the entire matrix generator, with no diagonal
or commutation reduction. -/
theorem fisherRaoMetric_congruenceTangent_nonneg
    (G H A : Mat) (hHG : H * G = 1) (hGH : G * H = 1) :
    0 ≤ fisherRaoMetric (Hᵀ * H)
      (congruenceTangent (G * Gᵀ) A) (congruenceTangent (G * Gᵀ) A) := by
  rw [fisherRaoMetric_congruenceTangent_eq_sum_sq G H A hHG hGH]
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- The nullspace is exactly the skew-adjoint whitened generator, the
infinitesimal stabilizer of the covariance congruence action. -/
theorem fisherRaoMetric_congruenceTangent_zero_iff
    (G H A : Mat) (hHG : H * G = 1) (hGH : G * H = 1) :
    fisherRaoMetric (Hᵀ * H)
        (congruenceTangent (G * Gᵀ) A) (congruenceTangent (G * Gᵀ) A) = 0 ↔
      (H * A * G)ᵀ = -(H * A * G) := by
  rw [fisherRaoMetric_congruenceTangent_gram G H A hHG hGH]
  have hsym : (H * A * G + (H * A * G)ᵀ)ᵀ =
      H * A * G + (H * A * G)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  rw [fisherRaoMetric_zero_iff_at_identity _ hsym]
  constructor
  · intro hzero
    calc
      (H * A * G)ᵀ =
          (H * A * G + (H * A * G)ᵀ) - H * A * G := by abel
      _ = -(H * A * G) := by rw [hzero]; simp
  · intro hskew
    rw [hskew]
    simp

end InfoGeometry.Architecture.MatrixSymmetricCone

end noncomputable section
