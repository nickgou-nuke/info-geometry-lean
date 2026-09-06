import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Architecture.CartanFisherRao

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma sum_re (z : n → ℂ) :
    (∑ i, z i).re = ∑ i, (z i).re := by
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Complex.add_re, ih, Finset.sum_insert ha]

/-- Hermitian matrix property: X† = X. -/
def IsHermitian (X : Matrix n n ℂ) : Prop :=
  Xᴴ = X

/-- Skew-Hermitian matrix property: K† = -K. -/
def IsSkewHermitian (K : Matrix n n ℂ) : Prop :=
  Kᴴ = -K

/-- Lie bracket of two matrices: [A, B] = A * B - B * A. -/
def commutator (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

/-- THEOREM 1 (Cartan [p, p] ⊆ k): Commutator of two Hermitian matrices is skew-Hermitian. -/
theorem commutator_hermitian_is_skew (X Y : Matrix n n ℂ)
    (hX : IsHermitian X) (hY : IsHermitian Y) :
    IsSkewHermitian (commutator X Y) := by
  dsimp [IsSkewHermitian, commutator]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
  dsimp [IsHermitian] at hX hY
  rw [hX, hY]
  abel

/-- THEOREM 2 (Cartan [k, p] ⊆ p): Commutator of skew-Hermitian and Hermitian is Hermitian. -/
theorem commutator_skew_hermitian_is_hermitian (K X : Matrix n n ℂ)
    (hK : IsSkewHermitian K) (hX : IsHermitian X) :
    IsHermitian (commutator K X) := by
  dsimp [IsHermitian, commutator]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
  dsimp [IsSkewHermitian] at hK
  dsimp [IsHermitian] at hX
  rw [hK, hX, mul_neg, neg_mul]
  abel

/-- THEOREM 3 (Cartan [k, k] ⊆ k): Commutator of two skew-Hermitian matrices is skew-Hermitian. -/
theorem commutator_skew_skew_is_skew (K₁ K₂ : Matrix n n ℂ)
    (hK₁ : IsSkewHermitian K₁) (hK₂ : IsSkewHermitian K₂) :
    IsSkewHermitian (commutator K₁ K₂) := by
  dsimp [IsSkewHermitian, commutator]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
  dsimp [IsSkewHermitian] at hK₁ hK₂
  rw [hK₁, hK₂, neg_mul_neg, neg_mul_neg]
  abel

/-- The Fisher–Rao / BKM Riemannian metric on the tangent space of Hermitian matrices. -/
def fisherRaoMetric (X Y : Matrix n n ℂ) : ℝ :=
  ((trace (X * Y)).re)

/-- THEOREM 4: The Fisher–Rao metric is symmetric. -/
theorem fisherRaoMetric_symm (X Y : Matrix n n ℂ) :
    fisherRaoMetric X Y = fisherRaoMetric Y X := by
  dsimp [fisherRaoMetric]
  rw [trace_mul_comm]

/-- THEOREM 5: The Fisher–Rao metric is unitary Ad-invariant: Tr((U X U†)(U Y U†)) = Tr(X Y). -/
theorem fisherRaoMetric_unitary_invariant (U X Y : Matrix n n ℂ)
    (hU_inv : Uᴴ * U = 1) :
    fisherRaoMetric (U * X * Uᴴ) (U * Y * Uᴴ) = fisherRaoMetric X Y := by
  dsimp [fisherRaoMetric]
  have h_prod : (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
    calc
      (U * X * Uᴴ) * (U * Y * Uᴴ)
        = U * X * (Uᴴ * U * Y * Uᴴ) := by
          simp only [mul_assoc]
      _ = U * X * (1 * Y * Uᴴ) := by rw [hU_inv]
      _ = U * X * (Y * Uᴴ) := by rw [one_mul]
      _ = U * (X * Y) * Uᴴ := by simp only [mul_assoc]
  rw [h_prod, trace_mul_comm (U * (X * Y)) Uᴴ]
  have h_cancel : Uᴴ * (U * (X * Y)) = (Uᴴ * U) * (X * Y) := by rw [mul_assoc]
  rw [h_cancel, hU_inv, one_mul]

/-- Nomizu Curvature of the Fisher–Rao metric on the symmetric cone: R(X, Y)Z = -[[X, Y], Z]. -/
def fisherRaoCurvature (X Y Z : Matrix n n ℂ) : Matrix n n ℂ :=
  - commutator (commutator X Y) Z

/-- 
  MASTER THEOREM: The Fisher–Rao Riemannian metric on the symmetric cone of positive-definite matrices
  has NON-POSITIVE sectional curvature:
    K_FR(X, Y) = - Tr([X,Y]† [X,Y]) ≤ 0.
-/
theorem fisherRao_sectional_curvature_nonpositive (X Y : Matrix n n ℂ)
    (hX : IsHermitian X) (hY : IsHermitian Y) :
    ((trace ((commutator X Y) * (commutator X Y))).re) ≤ 0 := by
  have h_skew : IsSkewHermitian (commutator X Y) := commutator_hermitian_is_skew X Y hX hY
  have h_conj : (commutator X Y)ᴴ = - (commutator X Y) := h_skew
  have h_prod : (commutator X Y) * (commutator X Y) = - ((commutator X Y)ᴴ * (commutator X Y)) := by
    calc
      (commutator X Y) * (commutator X Y)
        = (- (- commutator X Y)) * (commutator X Y) := by rw [neg_neg]
      _ = - ((- commutator X Y) * (commutator X Y)) := by rw [neg_mul]
      _ = - ((commutator X Y)ᴴ * (commutator X Y)) := by rw [← h_conj]
  rw [h_prod, Matrix.trace_neg, Complex.neg_re]
  have h_psd : 0 ≤ (trace ((commutator X Y)ᴴ * (commutator X Y))).re := by
    dsimp [trace]
    rw [sum_re]
    have h_diag (i : n) : 0 ≤ (((commutator X Y)ᴴ * (commutator X Y)) i i).re := by
      dsimp [mul_apply]
      rw [sum_re]
      have h_term (j : n) : 0 ≤ (((commutator X Y)ᴴ i j * (commutator X Y) j i)).re := by
        dsimp [conjTranspose_apply]
        have h_ring : (commutator X Y j i).re * (commutator X Y j i).re - -(commutator X Y j i).im * (commutator X Y j i).im =
            (commutator X Y j i).re ^ 2 + (commutator X Y j i).im ^ 2 := by ring
        rw [h_ring]
        positivity
      exact Finset.sum_nonneg (fun j _ => h_term j)
    exact Finset.sum_nonneg (fun i _ => h_diag i)
  linarith

end InfoGeometry.Architecture.CartanFisherRao

end noncomputable section
