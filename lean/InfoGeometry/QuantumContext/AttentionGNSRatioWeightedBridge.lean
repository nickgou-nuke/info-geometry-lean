/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import InfoGeometry.QuantumContext.MatrixGNS
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.AttentionStageColimitState
import InfoGeometry.QuantumContext.MarkovPetzRatioWeightedAdjoint

/-!
# Attention GNS transport of ratio-weighted range compression

The group-inverse range-compression owner uses the full-matrix ratio pairing
`Tr (Xᵀ Dπ Y Dπ⁻¹)`. The attention owner uses the GNS pairing
`Tr (Dπ Uᵀ V)`. For strictly positive weights, the invertible entrywise
change `Fπ(X)ᵢⱼ = sqrt(πᵢ) Xᵢⱼ / πⱼ` identifies these pairings. Consequently,
the *conjugated* range compression `Fπ ∘ (X ↦ E X E) ∘ Fπ⁻¹` is self-adjoint
for the attention GNS pairing when the supplied matrix satisfies
detailed balance for those same weights. This is a finite-stage theorem; it
does not assert detailed balance for generic attention or compatibility of
independently chosen stages.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionGNSRatioWeightedBridge

open Matrix
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Probability

variable {ι : Type*}

/-- Full-matrix change of coordinates from the ratio-weighted carrier to the
diagonal-state GNS carrier. -/
def ratioToGns (π : ι → ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (Real.sqrt (π i) / π j) * X i j

/-- Inverse entrywise change of coordinates to `ratioToGns`. -/
def gnsToRatio (π : ι → ℝ) (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => (π j / Real.sqrt (π i)) * X i j

theorem ratioToGns_gnsToRatio (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (X : Matrix ι ι ℝ) :
    ratioToGns π (gnsToRatio π X) = X := by
  ext i j
  have hπj : π j ≠ 0 := (hπ j).ne'
  have hsqrt : Real.sqrt (π i) ≠ 0 := (Real.sqrt_pos.mpr (hπ i)).ne'
  simp only [ratioToGns, gnsToRatio]
  field_simp [hπj, hsqrt]

theorem gnsToRatio_ratioToGns (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (X : Matrix ι ι ℝ) :
    gnsToRatio π (ratioToGns π X) = X := by
  ext i j
  have hπj : π j ≠ 0 := (hπ j).ne'
  have hsqrt : Real.sqrt (π i) ≠ 0 := (Real.sqrt_pos.mpr (hπ i)).ne'
  simp only [ratioToGns, gnsToRatio]
  field_simp [hπj, hsqrt]

private theorem ratioGns_scale_identity (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (i j : ι) :
    π j * ((Real.sqrt (π i) / π j) * (Real.sqrt (π i) / π j)) =
      π i / π j := by
  have hπj : π j ≠ 0 := (hπ j).ne'
  have hroot : Real.sqrt (π i) * Real.sqrt (π i) = π i := by
    rw [← pow_two, Real.sq_sqrt (le_of_lt (hπ i))]
  field_simp [hπj]
  nlinarith [hroot]

private theorem scalar_weight_product (c d x y : ℝ) :
    c * ((d * x) * (d * y)) = (c * (d * d)) * x * y := by
  ring

variable [Fintype ι] [DecidableEq ι]

private theorem gnsInner_diagonal_eq_sum (π : ι → ℝ)
    (X Y : Matrix ι ι ℝ) :
    MatrixGNS.gnsInner (Matrix.diagonal π) X Y =
      ∑ j, π j * ∑ i, X i j * Y i j := by
  rw [MatrixGNS.gnsInner_eq_trace, MatrixGNS.diagonal_trace_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1

/-- The ratio-weighted trace pairing is the attention-style diagonal GNS
pairing after `ratioToGns`. Both arguments range over the full matrix algebra. -/
theorem ratioWeightedPairing_eq_gnsAfterTransport (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (X Y : Matrix ι ι ℝ) :
    ratioWeightedMatrixPairing π X Y =
      MatrixGNS.gnsInner (Matrix.diagonal π)
        (ratioToGns π X) (ratioToGns π Y) := by
  rw [ratioWeightedMatrixPairing_eq_sum, gnsInner_diagonal_eq_sum]
  calc
    (∑ i, ∑ j, (π i / π j) * X i j * Y i j) =
        ∑ j, ∑ i, (π i / π j) * X i j * Y i j := by
          exact Finset.sum_comm
    _ = ∑ j, π j * ∑ i,
          ratioToGns π X i j * ratioToGns π Y i j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (π i / π j) * X i j * Y i j =
                (π j * ((Real.sqrt (π i) / π j) *
                  (Real.sqrt (π i) / π j))) * X i j * Y i j := by
                    rw [ratioGns_scale_identity π hπ i j]
            _ = π j *
                (ratioToGns π X i j * ratioToGns π Y i j) := by
                  simp only [ratioToGns]
                  exact (scalar_weight_product (π j)
                    (Real.sqrt (π i) / π j) (X i j) (Y i j)).symm

/-- The range compression conjugated by the ratio/GNS coordinate change.
Its definition makes the carrier transport explicit instead of silently
identifying two different weighted pairings. -/
def transportedMarkovCompression (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (X : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  ratioToGns π
    (markovRangeIdempotent P G * gnsToRatio π X * markovRangeIdempotent P G)

/-- Under detailed balance, the conjugated full-matrix range compression is
self-adjoint in the diagonal GNS pairing. The assumptions and conclusion are
finite-stage; no stochasticity or reversibility of arbitrary attention is
inferred. -/
theorem transportedMarkovCompression_gns_selfAdjoint
    (P G : Matrix ι ι ℝ) (π : ι → ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : DetailedBalance π P) (hπ : ∀ i, 0 < π i)
    (X Y : Matrix ι ι ℝ) :
    MatrixGNS.gnsInner (Matrix.diagonal π)
        (transportedMarkovCompression P G π X) Y =
      MatrixGNS.gnsInner (Matrix.diagonal π)
        X (transportedMarkovCompression P G π Y) := by
  calc
    MatrixGNS.gnsInner (Matrix.diagonal π)
        (transportedMarkovCompression P G π X) Y =
      ratioWeightedMatrixPairing π
        (markovRangeIdempotent P G * gnsToRatio π X * markovRangeIdempotent P G)
        (gnsToRatio π Y) := by
          change MatrixGNS.gnsInner (Matrix.diagonal π)
              (ratioToGns π
                (markovRangeIdempotent P G * gnsToRatio π X *
                  markovRangeIdempotent P G)) Y = _
          conv_lhs => rw [← ratioToGns_gnsToRatio π hπ Y]
          exact (ratioWeightedPairing_eq_gnsAfterTransport π hπ
            (markovRangeIdempotent P G * gnsToRatio π X *
              markovRangeIdempotent P G) (gnsToRatio π Y)).symm
    _ = ratioWeightedMatrixPairing π (gnsToRatio π X)
        (markovRangeIdempotent P G * gnsToRatio π Y * markovRangeIdempotent P G) :=
          ratioWeightedMatrixPairing_markovCompression_selfAdjoint P G π hG hDB hπ
            (gnsToRatio π X) (gnsToRatio π Y)
    _ = MatrixGNS.gnsInner (Matrix.diagonal π)
        (ratioToGns π (gnsToRatio π X))
        (ratioToGns π
          (markovRangeIdempotent P G * gnsToRatio π Y * markovRangeIdempotent P G)) :=
          ratioWeightedPairing_eq_gnsAfterTransport π hπ _ _
    _ = MatrixGNS.gnsInner (Matrix.diagonal π)
        X (transportedMarkovCompression P G π Y) := by
          change MatrixGNS.gnsInner (Matrix.diagonal π)
              (ratioToGns π (gnsToRatio π X))
              (ratioToGns π
                (markovRangeIdempotent P G * gnsToRatio π Y *
                  markovRangeIdempotent P G)) =
            MatrixGNS.gnsInner (Matrix.diagonal π) X
              (ratioToGns π
                (markovRangeIdempotent P G * gnsToRatio π Y *
                  markovRangeIdempotent P G))
          rw [ratioToGns_gnsToRatio π hπ X]

/-- Attention specialization on one finite matrix carrier. The matrix `P`
must satisfy detailed balance with the same softmax weights used by the
attention GNS state. -/
theorem attentionTransportedMarkovCompression_gns_selfAdjoint
    [Nonempty ι] (P G : Matrix ι ι ℝ)
    (logits : ι → ℝ) (β : ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : DetailedBalance (softmaxWeight logits β) P)
    (X Y : Matrix ι ι ℝ) :
    MatrixGNS.gnsInner (attentionDensityMatrix logits β)
        (transportedMarkovCompression P G (softmaxWeight logits β) X) Y =
      MatrixGNS.gnsInner (attentionDensityMatrix logits β)
        X (transportedMarkovCompression P G (softmaxWeight logits β) Y) := by
  simpa [attentionDensityMatrix] using
    transportedMarkovCompression_gns_selfAdjoint P G (softmaxWeight logits β)
      hG hDB (fun i => softmaxWeight_pos logits β i) X Y

/-- Selected-stage colimit readout of the finite attention GNS adjoint
identity. It is asserted only for the real observables injected at the chosen
stage, with detailed balance at that same stage. -/
theorem attentionSelectedColimit_transportedCompression_selfAdjoint
    (k : ℕ) (P G : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ)
    (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (hG : IsGroupInverse (1 - P) G)
    (hDB : DetailedBalance (softmaxWeight logits β) P)
    (X Y : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    selectedStageColimitFunctional k
        (AttentionStageColimitState.attentionStageDensity k logits β)
        (InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection k
          (AttentionStageColimitState.complexifyRealMatrix
            ((transportedMarkovCompression P G (softmaxWeight logits β) X)ᵀ *
              Y))) =
      selectedStageColimitFunctional k
        (AttentionStageColimitState.attentionStageDensity k logits β)
        (InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit.stageInjection k
          (AttentionStageColimitState.complexifyRealMatrix
            (Xᵀ *
              transportedMarkovCompression P G (softmaxWeight logits β) Y))) := by
  have hGNS := attentionTransportedMarkovCompression_gns_selfAdjoint
    P G logits β hG hDB X Y
  have hState :
      attentionState logits β
        ((transportedMarkovCompression P G (softmaxWeight logits β) X)ᵀ *
          Y) =
      attentionState logits β
        (Xᵀ *
          transportedMarkovCompression P G (softmaxWeight logits β) Y) := by
    simpa [MatrixGNS.gnsInner, attentionState, Matrix.mul_assoc] using hGNS
  rw [AttentionStageColimitState.attentionColimitFunctional_real_seed_readout,
    AttentionStageColimitState.attentionColimitFunctional_real_seed_readout]
  exact congrArg (algebraMap ℝ ℂ) hState

end InfoGeometry.QuantumContext.AttentionGNSRatioWeightedBridge
