import Mathlib

noncomputable section

namespace InfoGeometry.Quantum.KANFormalization

open Matrix
open scoped BigOperators

/-- Finite-level `K A N` packet over real matrices. -/
structure KANFactor (n : Type*) [Fintype n] [DecidableEq n] where
  K : Matrix n n ℝ
  A : Matrix n n ℝ
  N : Matrix n n ℝ

namespace KANFactor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Global modeled transfer operator. -/
def total (F : KANFactor n) : Matrix n n ℝ :=
  F.K * F.A * F.N

/-- Finite-level determinant decomposition. -/
theorem det_total (F : KANFactor n) :
    Matrix.det (total F) = Matrix.det F.K * Matrix.det F.A * Matrix.det F.N := by
  simp [total, Matrix.det_mul]

/-- Finite-level determinant multiplicativity for global models. -/
theorem det_mul (F G : KANFactor n) :
    Matrix.det (total F * total G) = Matrix.det (total F) * Matrix.det (total G) := by
  simp [Matrix.det_mul]

/--
Log-det bridge on modeled sectors: if each sector determinant is represented as an
exponential coordinate, `log ∘ det` becomes additive.
Conservative assumptions: only finite matrices and explicit nonzero/equality hypotheses.
-/
theorem log_det_additive_of_modeled_sectors
    (F : KANFactor n) (κ α ν : ℝ)
    (hK : Matrix.det F.K = Real.exp κ)
    (hA : Matrix.det F.A = Real.exp α)
    (hN : Matrix.det F.N = Real.exp ν) :
    Real.log (Matrix.det (total F)) = κ + α + ν := by
  have hK0 : Matrix.det F.K ≠ 0 := by simp [hK]
  have hA0 : Matrix.det F.A ≠ 0 := by simp [hA]
  have hN0 : Matrix.det F.N ≠ 0 := by simp [hN]
  rw [det_total]
  rw [Real.log_mul (mul_ne_zero hK0 hA0) hN0]
  rw [Real.log_mul hK0 hA0]
  simp [hK, hA, hN]

end KANFactor

end InfoGeometry.Quantum.KANFormalization
