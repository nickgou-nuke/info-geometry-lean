import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Section 4.4: Hyperkähler Symmetry — Lean 4 Formalization

Complex structures on M(2,ℂ) via Pauli left-multiplication:
  I(X) = i·σ₁·X
  J(X) = i·σ₂·X
  K(X) = -i·σ₃·X

Proved: quaternion relations, metric compatibility.
-/

noncomputable section

namespace Section4

open Matrix

def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Pauli basis array. -/
def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => I2 | 1 => s1 | 2 => s2 | 3 => s3

/-- I(X) = i·σ₁·X -/
def I_map (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • (s1 * X)

/-- J(X) = i·σ₂·X -/
def J_map (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • (s2 * X)

/-- K(X) = -i·σ₃·X -/
def K_map (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I) • (s3 * X)

/-- I² = -Id on the Pauli basis. -/
theorem I_sq_neg_id (a : Fin 4) : I_map (I_map (sigma a)) = - (sigma a) := by
  fin_cases a <;>
    simp [I_map, sigma, I2, s1, s2, s3]

/-- J² = -Id. -/
theorem J_sq_neg_id (a : Fin 4) : J_map (J_map (sigma a)) = - (sigma a) := by
  fin_cases a <;>
    simp [J_map, sigma, I2, s1, s2, s3]

/-- K² = -Id. -/
theorem K_sq_neg_id (a : Fin 4) : K_map (K_map (sigma a)) = - (sigma a) := by
  fin_cases a <;>
    simp [K_map, sigma, I2, s1, s2, s3]

/-- IJ = K. -/
theorem IJ_eq_K (a : Fin 4) : I_map (J_map (sigma a)) = K_map (sigma a) := by
  fin_cases a <;>
    simp [I_map, J_map, K_map, sigma, I2, s1, s2, s3]

/-- JK = I. -/
theorem JK_eq_I (a : Fin 4) : J_map (K_map (sigma a)) = I_map (sigma a) := by
  fin_cases a <;>
    simp [I_map, J_map, K_map, sigma, I2, s1, s2, s3]

/-- KI = J. -/
theorem KI_eq_J (a : Fin 4) : K_map (I_map (sigma a)) = J_map (sigma a) := by
  fin_cases a <;>
    simp [I_map, J_map, K_map, sigma, I2, s1, s2, s3]

/-- IJK = -Id. -/
theorem IJK_eq_neg_id (a : Fin 4) : I_map (J_map (K_map (sigma a))) = - (sigma a) := by
  fin_cases a <;>
    simp [I_map, J_map, K_map, sigma, I2, s1, s2, s3]

/-- Hermitian inner product: g(A,B) = ½·Tr(A†·B). -/
def hs (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ((star A * B).trace) / 2

/-- Metric compatibility: g(I(X), I(Y)) = g(X, Y) on Pauli basis. -/
theorem metric_compat_I (a b : Fin 4) :
    hs (I_map (sigma a)) (I_map (sigma b)) = hs (sigma a) (sigma b) := by
  fin_cases a <;> fin_cases b <;>
    simp [hs, I_map, sigma, I2, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace,
      Complex.conj_I]

/-- Metric compatibility: g(J(X), J(Y)) = g(X, Y). -/
theorem metric_compat_J (a b : Fin 4) :
    hs (J_map (sigma a)) (J_map (sigma b)) = hs (sigma a) (sigma b) := by
  fin_cases a <;> fin_cases b <;>
    simp [hs, J_map, sigma, I2, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace,
      Complex.conj_I]

/-- Metric compatibility: g(K(X), K(Y)) = g(X, Y). -/
theorem metric_compat_K (a b : Fin 4) :
    hs (K_map (sigma a)) (K_map (sigma b)) = hs (sigma a) (sigma b) := by
  fin_cases a <;> fin_cases b <;>
    simp [hs, K_map, sigma, I2, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace,
      Complex.conj_I]

end Section4
