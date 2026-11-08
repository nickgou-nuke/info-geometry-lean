/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovRangeOrthogonalProjection
import InfoGeometry.QuantumContext.MarkovWeightedMatrixTrace

/-!
# Ratio-weighted adjointness of two-sided range-idempotent compression

For a finite matrix `P`, a supplied group inverse of `1 - P`, detailed balance,
and strictly positive weights, the range idempotent defines a self-adjoint
two-sided compression for the full-matrix ratio-weighted trace pairing. The
name `markovRangeIdempotent` is inherited from its existing owner; this theorem
does not assume that `P` is stochastic or prove a Markov transition, stationary
state, or positive-channel property. The carrier is the full matrix algebra,
with no diagonal restriction.
-/

namespace InfoGeometry.QuantumContext.MarkovDrazin

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ratio-weighted bilinear pairing on the full matrix carrier, written as a
finite-stage trace expression. It is positive definite when all weights are
strictly positive; for arbitrary weights the definition asserts only a real
bilinear pairing, not an inner product. -/
noncomputable def ratioWeightedMatrixPairing (π : ι → ℝ) (X Y : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (Xᵀ * Matrix.diagonal π * Y *
    Matrix.diagonal (fun i => (π i)⁻¹))

/-- Entrywise readout of the ratio-weighted trace pairing. -/
theorem ratioWeightedMatrixPairing_eq_sum
    (π : ι → ℝ) (X Y : Matrix ι ι ℝ) :
    ratioWeightedMatrixPairing π X Y =
      ∑ i, ∑ j, (π i / π j) * X i j * Y i j := by
  classical
  unfold ratioWeightedMatrixPairing
  simp [Matrix.trace, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.diagonal, div_eq_mul_inv, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem markovRangeIdempotent_detailedBalance
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : DetailedBalance π P) (hπ : ∀ i, π i ≠ 0) :
    DetailedBalance π (markovRangeIdempotent P G) := by
  have hP := (detailedBalance_iff_weightedAdjoint_eq π P hπ).mp hDB
  have hL : weightedAdjoint π (1 - P) = 1 - P := by
    rw [weightedAdjoint_sub, weightedAdjoint_one π hπ, hP]
  have hGself := weightedAdjoint_groupInverse_self π (1 - P) G hπ hL hG
  have hEself : weightedAdjoint π (markovRangeIdempotent P G) =
      markovRangeIdempotent P G := by
    rw [markovRangeIdempotent, weightedAdjoint_mul π (1 - P) G hπ,
      hGself, hL]
    exact hG.2.2.symm
  exact (detailedBalance_iff_weightedAdjoint_eq π
    (markovRangeIdempotent P G) hπ).mpr hEself

/-- The two-sided range-idempotent compression associated with `1 - P` is
self-adjoint for the ratio-weighted full-matrix pairing under detailed balance
and strictly positive weights. No stochasticity assumption on `P` is used. -/
theorem ratioWeightedMatrixPairing_markovCompression_selfAdjoint
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : DetailedBalance π P) (hπ : ∀ i, 0 < π i)
    (X Y : Matrix ι ι ℝ) :
    ratioWeightedMatrixPairing π
        (markovRangeIdempotent P G * X * markovRangeIdempotent P G) Y =
      ratioWeightedMatrixPairing π X
        (markovRangeIdempotent P G * Y * markovRangeIdempotent P G) := by
  let E := markovRangeIdempotent P G
  let D := Matrix.diagonal π
  let Dinv := Matrix.diagonal (fun i => (π i)⁻¹)
  have hπne : ∀ i, π i ≠ 0 := fun i => (hπ i).ne'
  have hDBE : DetailedBalance π E := by
    simpa [E] using markovRangeIdempotent_detailedBalance P G π hG hDB hπne
  have hED : D * E = Eᵀ * D := by
    have h := hDBE
    exact sub_eq_zero.mp (by simpa [DetailedBalance, detailedBalanceResidual,
      stationaryWeightMatrix, D] using h)
  have hDinvE : Dinv * Eᵀ = E * Dinv := by
    ext i j
    have hentry := congrFun (congrFun hED j) i
    have hentry' : π j * E j i = E i j * π i := by
      simpa [D, Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply] using hentry
    simp [Dinv, Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply]
    field_simp [hπne i, hπne j]
    nlinarith [hentry']
  change Matrix.trace ((E * X * E)ᵀ * D * Y * Dinv) =
    Matrix.trace (Xᵀ * D * (E * Y * E) * Dinv)
  calc
    Matrix.trace ((E * X * E)ᵀ * D * Y * Dinv) =
        Matrix.trace (Eᵀ * Xᵀ * (Eᵀ * D) * Y * Dinv) := by
          congr 1
          simp only [Matrix.transpose_mul]
          noncomm_ring
    _ = Matrix.trace (Eᵀ * (Xᵀ * D * E * Y * Dinv)) := by
          congr 1
          rw [← hED]
          noncomm_ring
    _ = Matrix.trace ((Xᵀ * D * E * Y * Dinv) * Eᵀ) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Xᵀ * D * E * Y * E * Dinv) := by
          congr 1
          calc
            (Xᵀ * D * E * Y * Dinv) * Eᵀ =
                (Xᵀ * D * E * Y) * (Dinv * Eᵀ) := by noncomm_ring
            _ = (Xᵀ * D * E * Y) * (E * Dinv) := by rw [hDinvE]
            _ = Xᵀ * D * E * Y * E * Dinv := by noncomm_ring
    _ = Matrix.trace (Xᵀ * D * (E * Y * E) * Dinv) := by
          congr 1
          noncomm_ring

end InfoGeometry.QuantumContext.MarkovDrazin
