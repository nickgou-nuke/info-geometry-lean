/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevInteriorPairing

/-! The neutral Krein relative operator of the literal chain interior coefficient
pairing. This is a real coefficient carrier, not the many-body operator space
or the boundary Dirac trace Gram matrix. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevInteriorKrein
open Matrix KitaevChainCoefficients KitaevInteriorPairing
open InfoGeometry.Physics.MajoranaKreinPfaffianCarrier
variable {N : ℕ}

def interiorRelative (t : ℝ) :
    Matrix (Sum (Fin (N - 1)) (Fin (N - 1)))
      (Sum (Fin (N - 1)) (Fin (N - 1))) ℝ :=
  neutralKreinMetric * (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex

theorem interiorRelative_eq_grading (t : ℝ) :
    interiorRelative (N := N) t = -(2 * t) • polarizationGrading := by
  unfold interiorRelative
  rw [chain_interior_eq_offDiagonalPairing, majoranaRelativeEndomorphism_eq_blockDiagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;> simp [polarizationGrading, h]

theorem interiorRelative_sq (t : ℝ) :
    interiorRelative (N := N) t * interiorRelative t = ((2 * t)^2) • 1 := by
  rw [interiorRelative_eq_grading, smul_mul_smul, polarizationGrading_sq]
  congr 1
  ring

/-- Exchanging the two interior halves reverses the relative operator. -/
theorem interiorRelative_exchange (t : ℝ) :
    polarizationExchange * interiorRelative (N := N) t * polarizationExchange =
      -interiorRelative t := by
  rw [interiorRelative_eq_grading]
  simp only [mul_smul_comm, smul_mul_assoc]
  rw [polarizationExchange_anticommutes_grading, neg_mul, mul_assoc,
    polarizationExchange_sq, mul_one, smul_neg]

/-- The two-site, nonzero-coupling interior is not the zero operator. -/
theorem twoSite_interiorRelative_ne_zero : interiorRelative (N := 2) 1 ≠ 0 := by
  intro h
  have he := congrArg (fun M => M (Sum.inl 0) (Sum.inl 0)) h
  rw [interiorRelative_eq_grading] at he
  norm_num [polarizationGrading] at he

/-- The actual interior coefficient operator has the opposite square sign
from its neutral-metric relative operator. -/
theorem chain_interior_sq (t : ℝ) :
    (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex *
      (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex =
      (-((2 * t)^2)) • 1 := by
  rw [chain_interior_eq_offDiagonalPairing]
  simp only [offDiagonalPairing, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;>
    simp [Matrix.transpose_smul, h, pow_two]

/-- Skew transpose and neutral-metric selfadjointness coexist on the actual
interior coefficient carrier. This uses the metric adjoint, not transpose alone. -/
theorem chain_interior_krein_fixed (t : ℝ) :
    neutralKreinMetric *
      ((chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex).transpose *
        neutralKreinMetric =
      (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex := by
  rw [chain_interior_eq_offDiagonalPairing]
  simp only [neutralKreinMetric, offDiagonalPairing, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

end InfoGeometry.Canonical.KitaevInteriorKrein
