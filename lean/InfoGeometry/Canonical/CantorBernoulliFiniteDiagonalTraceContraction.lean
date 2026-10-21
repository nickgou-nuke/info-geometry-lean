/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge

/-!
# The finite diagonal map into Bernoulli boundary `L²`

This owner starts the full-matrix-to-boundary bridge at the exact finite
BitWord matrix carrier.  It proves the diagonal square-sum contraction and
compatibility with the existing dyadic matrix and diagonal successor maps.
It does not yet identify the matrix square-sum with a completed GNS vector or
extend the map to the filtered GNS colimit.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceContraction

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorBernoulliFiniteDiagL2Embedding
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge

/-- The algebraic diagonal of a finite bit-word matrix, in the existing
diagonal stage. -/
def diagonalPart (n : ℕ) (A : BitWordMatrixStage n) : DiagAlg n :=
  Matrix.diag A

/-- The diagonal square-sum is bounded by the full finite
Hilbert--Schmidt square-sum. -/
theorem diagonal_normSq_sum_le_hs_normSq_sum
    (n : ℕ) (A : BitWordMatrixStage n) :
    (∑ u : BitWord n, Complex.normSq (A u u)) ≤
      ∑ u : BitWord n, ∑ v : BitWord n, Complex.normSq (A v u) := by
  classical
  apply Finset.sum_le_sum
  intro u hu
  exact Finset.single_le_sum
    (fun v hv => Complex.normSq_nonneg (A v u))
    (Finset.mem_univ u)

/-- The same diagonal contraction with normalized finite counting measure. -/
theorem normalized_diagonal_normSq_sum_le_hs_normSq_sum
    (n : ℕ) (A : BitWordMatrixStage n) :
    (1 / (Fintype.card (BitWord n) : ℝ)) *
        (∑ u : BitWord n, Complex.normSq (A u u)) ≤
      (1 / (Fintype.card (BitWord n) : ℝ)) *
        (∑ u : BitWord n, ∑ v : BitWord n,
          Complex.normSq (A v u)) := by
  apply mul_le_mul_of_nonneg_left
    (diagonal_normSq_sum_le_hs_normSq_sum n A)
  positivity

/-- Diagonal extraction commutes with the existing BitWord matrix successor;
the diagonal successor is the canonical prefix-cylinder embedding. -/
theorem diagonalPart_bond_compatible
    (n : ℕ) (A : BitWordMatrixStage n) :
    diagonalPart (n + 1) (ComplexMatrixStage.bondFun n A) =
      diagEmbedSucc n (diagonalPart n A) := by
  ext w
  simp [diagonalPart, ComplexMatrixStage.bondFun,
    diagEmbedSucc, prefixSucc]

/-- The boundary `L²` inner product of the extracted diagonal is exactly the
existing normalized diagonal trace pairing. -/
theorem diagonalCylinderL2_inner_diagonalPart
    (n : ℕ) (A : BitWordMatrixStage n) :
    inner ℂ (diagonalCylinderL2 n (diagonalPart n A))
      (diagonalCylinderL2 n (diagonalPart n A)) =
        DiagTrace n (fun u => star (A u u) * A u u) := by
  exact diagonalCylinderL2_inner n (diagonalPart n A) (diagonalPart n A)

end InfoGeometry.Canonical.CantorBernoulliFiniteDiagonalTraceContraction

end
