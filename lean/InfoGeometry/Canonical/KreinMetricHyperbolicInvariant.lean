import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hyperbolic frame pullback of a symmetric matrix metric

This is the finite associative matrix lemma behind the gauge/isometry branch.
It deliberately does not identify a split-octonionic generator with a matrix
generator; that representation datum is owned elsewhere.
-/

namespace InfoGeometry.Canonical.KreinMetric

open Matrix

noncomputable section

variable {n : ℕ}

def transportedFrame (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Real.cosh t • (1 : Matrix (Fin n) (Fin n) ℝ) + Real.sinh t • X

def transportedKreinMetric (G₀ X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  transpose (transportedFrame X t) * G₀ * transportedFrame X t

def X_skew (G₀ X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  transpose X * G₀ + G₀ * X = 0

def X_sym_tensor (G₀ X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  transpose X * G₀ + G₀ * X

theorem transportedKreinMetric_constant_of_skew
    (G₀ X : Matrix (Fin n) (Fin n) ℝ) (hX_sq : X * X = 1)
    (hskew : X_skew G₀ X) (t : ℝ) :
    transportedKreinMetric G₀ X t = G₀ := by
  unfold transportedKreinMetric transportedFrame
  unfold X_skew at hskew
  have htranspose :
      transpose
          (Real.cosh t • (1 : Matrix (Fin n) (Fin n) ℝ) +
            Real.sinh t • X) =
        Real.cosh t • (1 : Matrix (Fin n) (Fin n) ℝ) +
          Real.sinh t • transpose X := by
    simp [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
  rw [htranspose]
  have hXmetric : transpose X * G₀ * X = -G₀ := by
    calc
      transpose X * G₀ * X =
          (transpose X * G₀ + G₀ * X) * X - (G₀ * X) * X := by
            noncomm_ring
      _ = -(G₀ * X) * X := by
        rw [hskew, zero_mul, zero_sub, neg_mul]
      _ = -(G₀ * (X * X)) := by
        rw [neg_mul]
        exact congrArg Neg.neg (mul_assoc G₀ X X)
      _ = -G₀ := by rw [hX_sq, mul_one]
  have hXtG : transpose X * G₀ = -(G₀ * X) :=
    eq_neg_of_add_eq_zero_left hskew
  have hGXX : (G₀ * X) * X = G₀ := by
    calc
      (G₀ * X) * X = G₀ * (X * X) := by noncomm_ring
      _ = G₀ := by rw [hX_sq, mul_one]
  have hnegGXX : -(G₀ * X) * X = -G₀ := by
    calc
      -(G₀ * X) * X = -((G₀ * X) * X) := by noncomm_ring
      _ = -G₀ := by rw [hGXX]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  rw [hXtG, hnegGXX]
  simp only [smul_add, smul_neg, smul_smul]
  calc
    _ = (Real.cosh t ^ 2 - Real.sinh t ^ 2) • G₀ := by module
    _ = G₀ := by rw [Real.cosh_sq_sub_sinh_sq, one_smul]

/-! This is an algebraic variation tensor, not a derivative theorem. -/
theorem metric_variation_tensor
    (G₀ X : Matrix (Fin n) (Fin n) ℝ) :
    X_sym_tensor G₀ X = transpose X * G₀ + G₀ * X := rfl

theorem metric_variation_nonzero_iff_sym_tensor_nonzero
    (G₀ X : Matrix (Fin n) (Fin n) ℝ) :
    X_sym_tensor G₀ X ≠ 0 ↔ transpose X * G₀ + G₀ * X ≠ 0 := Iff.rfl

end

end InfoGeometry.Canonical.KreinMetric
