import InfoGeometry.Canonical.SpinorialCore.Bipartite
import InfoGeometry.Canonical.SpinorialCore.FiniteIndex

/-!
# Polynomial supersymmetric index

Nonconstant powers of the two finite partner Laplacians have the same trace.
Consequently a normalized polynomial supertrace equals the dimension defect.
No analytic exponential or infinite-dimensional heat-kernel assertion is assumed.
-/

noncomputable section
open scoped BigOperators
namespace InfoGeometry.Canonical.SpinorialCore

variable {R m n : Type*} [CommRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Rectangular intertwining of powers of partner operators. -/
theorem partner_power_intertwines (A : Matrix m n R) (B : Matrix n m R) (k : ℕ) :
    (A * B) ^ k * A = A * (B * A) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (A * B) ^ (k + 1) * A = (A * B) ^ k * (A * (B * A)) := by
        rw [pow_succ]
        simp only [Matrix.mul_assoc]
      _ = ((A * B) ^ k * A) * (B * A) := by rw [Matrix.mul_assoc]
      _ = (A * (B * A) ^ k) * (B * A) := by rw [ih]
      _ = A * (B * A) ^ (k + 1) := by rw [pow_succ, Matrix.mul_assoc]

theorem partner_positive_power_trace (A : Matrix m n R) (B : Matrix n m R) (k : ℕ) :
    Matrix.trace ((A * B) ^ (k + 1)) = Matrix.trace ((B * A) ^ (k + 1)) := by
  calc
    Matrix.trace ((A * B) ^ (k + 1)) =
        Matrix.trace (((A * B) ^ k * A) * B) := by rw [pow_succ, Matrix.mul_assoc]
    _ = Matrix.trace ((A * (B * A) ^ k) * B) := by rw [partner_power_intertwines]
    _ = Matrix.trace (B * (A * (B * A) ^ k)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((B * A) * (B * A) ^ k) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((B * A) ^ (k + 1)) := by rw [pow_succ']

/-- Full finite polynomial supertrace, with the constant-term normalization explicit. -/
theorem polynomial_supertrace (N : ℕ) (c : Fin (N + 1) → R)
    (A : Matrix m n R) (B : Matrix n m R) :
    polynomialTrace N c (A * B) - polynomialTrace N c (B * A) =
      c 0 * ((Fintype.card m : R) - (Fintype.card n : R)) := by
  unfold polynomialTrace
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Matrix.trace_one, Fin.val_succ]
  have hs :
      (∑ i : Fin N, c i.succ * Matrix.trace ((A * B) ^ ((i : ℕ) + 1))) =
      (∑ i : Fin N, c i.succ * Matrix.trace ((B * A) ^ ((i : ℕ) + 1))) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [partner_positive_power_trace]
  rw [hs]
  ring

/-- In the real network carrier, normalization makes the polynomial index integral. -/
theorem normalized_network_supertrace (black white N : ℕ)
    (c : Fin (N + 1) → ℝ) (hc : c 0 = 1)
    (A : Matrix (Fin black) (Fin white) ℝ)
    (B : Matrix (Fin white) (Fin black) ℝ) :
    polynomialTrace N c (A * B) - polynomialTrace N c (B * A) =
      (vertexDefect black white : ℝ) := by
  rw [polynomial_supertrace, hc]
  simp [vertexDefect]

end InfoGeometry.Canonical.SpinorialCore
