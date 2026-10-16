/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovNaturalGradientMetric
import InfoGeometry.QuantumContext.MarkovFullMatrixGreen

/-!
# Orthogonality of the Markov group-inverse range projection

Under weighted detailed balance, the group-inverse range idempotent is
self-adjoint for the weighted Frobenius pairing on the full matrix carrier.
Together with its existing idempotence and the positive definiteness of the
pairing for positive weights, this makes it an orthogonal projection. The
result is stated for arbitrary full matrices; it is not a coordinatewise or
commutative reduction.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The group-inverse range idempotent is self-adjoint in the weighted
Frobenius pairing when the operator satisfies weighted detailed balance and
the weights are nonzero. -/
theorem weightedMatrixPairing_markovRange_selfAdjoint
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, π i ≠ 0) (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π (markovRangeIdempotent P G * X) Y =
      weightedMatrixPairing π X (markovRangeIdempotent P G * Y) := by
  change weightedMatrixPairing π (((1 - P) * G) * X) Y =
    weightedMatrixPairing π X (((1 - P) * G) * Y)
  calc
    weightedMatrixPairing π (((1 - P) * G) * X) Y =
        weightedMatrixPairing π ((1 - P) * (G * X)) Y := by
          congr 1
          noncomm_ring
    _ = weightedMatrixPairing π (G * X) ((1 - P) * Y) := by
          exact (weightedMatrixPairing_laplacian_symmetric P π
            (G * X) Y hDB).symm
    _ = weightedMatrixPairing π X (G * ((1 - P) * Y)) := by
          exact (weightedMatrixPairing_groupInverse_symmetric
            P G π X ((1 - P) * Y) hπ hDB hG).symm
    _ = weightedMatrixPairing π X (((1 - P) * G) * Y) := by
          congr 1
          calc
            G * ((1 - P) * Y) = (G * (1 - P)) * Y := by
              rw [mul_assoc]
            _ = ((1 - P) * G) * Y := by rw [hG.2.2]

/-- Idempotence and self-adjointness characterize the group-inverse range map
as an orthogonal projection for the positive weighted Frobenius inner product.
Detailed balance is the exact symmetry hypothesis needed here; stochasticity
is not used by this algebraic projection theorem. -/
theorem markovRange_is_orthogonalProjection
    [Nontrivial ι]
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, 0 < π i) :
    markovRangeIdempotent P G * markovRangeIdempotent P G =
        markovRangeIdempotent P G ∧
      (∀ X Y : Matrix ι ι ℝ,
        weightedMatrixPairing π (markovRangeIdempotent P G * X) Y =
          weightedMatrixPairing π X (markovRangeIdempotent P G * Y)) := by
  constructor
  · exact markovRangeIdempotent_idempotent P G hG
  · intro X Y
    exact weightedMatrixPairing_markovRange_selfAdjoint P G π hG hDB
      (fun i => (hπ i).ne') X Y

/-- The range and complementary projections are orthogonal in both orders for
the detailed-balance weighted pairing. -/
theorem weightedMatrixPairing_markovRange_complement_orthogonal
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (hπ : ∀ i, π i ≠ 0) (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π (markovRangeIdempotent P G * X)
        ((1 - markovRangeIdempotent P G) * Y) = 0 ∧
      weightedMatrixPairing π ((1 - markovRangeIdempotent P G) * X)
        (markovRangeIdempotent P G * Y) = 0 := by
  constructor
  · rw [weightedMatrixPairing_markovRange_selfAdjoint P G π hG hDB hπ X
      ((1 - markovRangeIdempotent P G) * Y)]
    rw [← mul_assoc, markovRange_mul_kernelComplement_eq_zero P G hG,
      zero_mul]
    simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]
  · rw [weightedMatrixPairing_comm]
    rw [weightedMatrixPairing_markovRange_selfAdjoint P G π hG hDB hπ Y
      ((1 - markovRangeIdempotent P G) * X)]
    rw [← mul_assoc, markovRange_mul_kernelComplement_eq_zero P G hG,
      zero_mul]
    simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]

end InfoGeometry.QuantumContext.MarkovDrazin
