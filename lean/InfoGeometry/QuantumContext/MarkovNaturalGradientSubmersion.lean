/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NaturalGradientSubmersionFlow
import InfoGeometry.QuantumContext.MarkovGroupInverseStationaryProjection
import InfoGeometry.QuantumContext.MarkovMetriplecticFlowBridge

/-!
# Markov group-inverse projectors as a full-matrix submersion split

The horizontal projection is left multiplication by the group-inverse range
idempotent `(1 - P) * G`; the vertical projection is left multiplication by
its complement. Under detailed balance these complementary projections are
orthogonal for the existing stationary-weighted Frobenius pairing. The pairing
is only asserted symmetric and block-orthogonal here: this module does not
claim nondegeneracy, positive definiteness, a natural-gradient inverse, or a
flow theorem.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin

open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bundle the existing full-matrix weighted pairing as a bilinear form. -/
def weightedMatrixBilin (π : ι → ℝ) :
    LinearMap.BilinForm ℝ (Matrix ι ι ℝ) :=
  LinearMap.mk₂ ℝ (weightedMatrixPairing π)
    (by
      intro X Y Z
      unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
      simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add, add_mul])
    (by
      intro c X Y
      unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
      change (∑ j, ∑ i, π i * (c * X i j) * Y i j) =
        c * (∑ j, ∑ i, π i * X i j * Y i j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ac_rfl)
    (by
      intro X Y Z
      unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
      simp only [Matrix.add_apply, Finset.sum_add_distrib, mul_add])
    (by
      intro c X Y
      unfold weightedMatrixPairing weightedMarkovPairing matrixColumn
      change (∑ j, ∑ i, π i * X i j * (c * Y i j)) =
        c * (∑ j, ∑ i, π i * X i j * Y i j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ac_rfl)

/-- The group-inverse range and stationary-kernel projections split the full
matrix module by left multiplication. -/
noncomputable def markovGroupInverseSubmersionSplit
    (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    SubmersionSplit (Matrix ι ι ℝ) where
  projH := mulLeftLinearMap ι ℝ (markovRangeIdempotent P G)
  projV := mulLeftLinearMap ι ℝ (markovStationaryProjector P G)
  sum_id := by
    intro X
    change markovRangeIdempotent P G * X +
      markovStationaryProjector P G * X = X
    have hsum : markovRangeIdempotent P G +
        markovStationaryProjector P G = 1 := by
      dsimp [markovStationaryProjector]
      exact markovRange_kernelComplement_sum P G
    rw [← add_mul, hsum, one_mul]
  idemH := by
    intro X
    change markovRangeIdempotent P G *
      (markovRangeIdempotent P G * X) = markovRangeIdempotent P G * X
    rw [← mul_assoc, markovRangeIdempotent_idempotent P G hG]
  idemV := by
    intro X
    change (1 - markovRangeIdempotent P G) *
      ((1 - markovRangeIdempotent P G) * X) =
        (1 - markovRangeIdempotent P G) * X
    rw [← mul_assoc, markovRangeComplement_idempotent P G hG]
  orthoHV := by
    intro X
    change markovRangeIdempotent P G *
      ((1 - markovRangeIdempotent P G) * X) = 0
    rw [← mul_assoc, markovRange_mul_kernelComplement_eq_zero P G hG,
      zero_mul]
  orthoVH := by
    intro X
    change (1 - markovRangeIdempotent P G) *
      (markovRangeIdempotent P G * X) = 0
    rw [← mul_assoc, markovKernelComplement_mul_range_eq_zero P G hG,
      zero_mul]

/-- Detailed balance makes the group-inverse range and stationary-kernel
parts orthogonal in the full-matrix weighted pairing. The proof uses the
Laplacian symmetry and its annihilation of the stationary projection; it does
not require the group inverse itself to be self-adjoint. -/
theorem weightedMatrixPairing_markovRange_kernel_orthogonal
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance π P)
    (X Y : Matrix ι ι ℝ) :
    weightedMatrixPairing π
      (markovRangeIdempotent P G * X)
      (markovStationaryProjector P G * Y) = 0 := by
  have hvertical : markovLeftOnsager P
      (markovStationaryProjector P G * Y) = 0 := by
    rw [markovLeftOnsager_apply]
    rw [← mul_assoc]
    change ((1 - P) * markovStationaryProjector P G) * Y = 0
    rw [laplacian_mul_markovStationaryProjector_eq_zero P G hG, zero_mul]
  have hhorizontal : markovRangeIdempotent P G * X =
      markovLeftOnsager P (G * X) := by
    change ((1 - P) * G) * X = (1 - P) * (G * X)
    exact mul_assoc (1 - P) G X
  rw [hhorizontal, ← weightedMatrixPairing_laplacian_symmetric P π
    (G * X) (markovStationaryProjector P G * Y) hDB, hvertical]
  simp [weightedMatrixPairing, weightedMarkovPairing, matrixColumn]

/-- Instantiate the generic natural-gradient submersion interface with the
Markov group-inverse split on full matrices and the detailed-balance pairing.
The generic interface records symmetry and horizontal/vertical orthogonality;
positive definiteness and gradient existence are not fields of that API. -/
noncomputable def markovNaturalGradientSubmersionSystem
    (P : Matrix ι ι ℝ) (π : ι → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hDB : InfoGeometry.Probability.DetailedBalance π P) :
    NaturalGradientSubmersionSystem (Matrix ι ι ℝ) := by
  let hExists := exists_stochastic_markovRangeIdempotent P hP
  let G := Classical.choose hExists
  have hG : IsGroupInverse (1 - P) G := Classical.choose_spec hExists
  exact {
    split := markovGroupInverseSubmersionSplit P G hG
    g := weightedMatrixBilin π
    symm := by
      intro X Y
      exact weightedMatrixPairing_comm π X Y
    ortho_HV := by
      intro X Y
      exact weightedMatrixPairing_markovRange_kernel_orthogonal P G π hG hDB X Y
  }

end InfoGeometry.QuantumContext.MarkovDrazin

end
