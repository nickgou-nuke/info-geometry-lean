import InfoGeometry.OperatorAlgebra.LieJordanDuality

/-!
# Noncommutative Dirac-type products and operator-valued Schur factorization

All coefficients live in an arbitrary associative ring, so they can be full
matrices or endomorphisms. A Clifford square retains the four gamma/transport
commutators. The block factorization has noncommuting operator entries; no
scalar determinant or simultaneous diagonalization is used.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorDiracSchur

variable {A : Type*} [Ring A]

/-- A two-generator algebraic Dirac expression, not a differential operator by fiat. -/
def dirac2 (g₁ g₂ a b : A) : A := g₁ * a + g₂ * b

/-- The complete square includes the defects of moving coefficients past gammas. -/
theorem dirac2_square (g₁ g₂ a b : A) :
    dirac2 g₁ g₂ a b * dirac2 g₁ g₂ a b =
      (g₁ * g₁) * a * a + (g₂ * g₂) * b * b +
      g₁ * g₂ * (a * b - b * a) +
      (g₁ * (a * g₁ - g₁ * a) * a + g₁ * (a * g₂ - g₂ * a) * b +
       g₂ * (b * g₁ - g₁ * b) * a + g₂ * (b * g₂ - g₂ * b) * b) +
      (g₁ * g₂ + g₂ * g₁) * b * a := by
  unfold dirac2
  noncomm_ring

/-- Even a genuine Clifford pair does not remove coefficient/gamma defects. -/
theorem clifford_square_with_defect (g₁ g₂ a b : A)
    (h₁ : g₁ * g₁ = 1) (h₂ : g₂ * g₂ = 1) (h₁₂ : g₁ * g₂ + g₂ * g₁ = 0) :
    dirac2 g₁ g₂ a b * dirac2 g₁ g₂ a b =
      a * a + b * b + g₁ * g₂ * (a * b - b * a) +
      (g₁ * (a * g₁ - g₁ * a) * a + g₁ * (a * g₂ - g₂ * a) * b +
       g₂ * (b * g₁ - g₁ * b) * a + g₂ * (b * g₂ - g₂ * b) * b) := by
  rw [dirac2_square, h₁, h₂, h₁₂]
  simp only [one_mul, zero_mul, add_zero]

/-- Polarization of two noncommuting operator components. -/
theorem dual_dirac_symmetric_product (D K : A) :
    (D + K) * (D - K) + (D - K) * (D + K) = 2 • (D * D - K * K) := by
  simp only [two_nsmul]
  noncomm_ring

theorem dual_dirac_bracket (D K : A) :
    (D + K) * (D - K) - (D - K) * (D + K) = -(2 • (D * K - K * D)) := by
  simp only [two_nsmul]
  noncomm_ring

open Matrix

/-- LDU factorization over any noncommutative operator coefficient ring.
The order of `c * u * b` in the Schur complement is essential. -/
theorem operator_block_LDU (a b c d u : A) (hau : a * u = 1) (hua : u * a = 1) :
    (!![1, 0; c * u, 1] : Matrix (Fin 2) (Fin 2) A) *
      !![a, 0; 0, d - c * u * b] * !![1, u * b; 0, 1] = !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;>
    noncomm_ring [hau, hua]

/-- The lower triangular factor has the displayed two-sided inverse. -/
theorem lower_unipotent_inverse (c : A) :
    (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, 0; -c, 1] = 1 ∧
    (!![1, 0; -c, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, 0; c, 1] = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper triangular factor has the displayed two-sided inverse. -/
theorem upper_unipotent_inverse (b : A) :
    (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, -b; 0, 1] = 1 ∧
    (!![1, -b; 0, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, b; 0, 1] = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.OperatorAlgebra.OperatorDiracSchur
