/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift
import InfoGeometry.QuantumContext.PetzRecoveryMartingale

/-!
# Markov group-inverse range projection and Petz compression

For a finite row-stochastic matrix `P` with group inverse `G` of `1 - P`,
the regular idempotent `E = (1 - P) * G` and its complement form an algebraic
support split in the full matrix ring. The induced compression `X ↦ E X E`
is idempotent. Here `E` is the (generally oblique) range projection of the
Markov Laplacian; this file does not identify it with a density support or an
orthogonal/symmetric projector. The word Petz refers only to the repository's
algebraic compression map `X ↦ E * X * E`, not to a state-dependent channel.
-/

namespace InfoGeometry.QuantumContext

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.PetzMartingale

/-- The range idempotent of a Markov Laplacian and a chosen group inverse. -/
def markovRangeIdempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P G : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 - P) * G

/-- Idempotence of the Markov Laplacian's group-inverse range projection. -/
theorem markovRangeIdempotent_idempotent {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovRangeIdempotent P G * markovRangeIdempotent P G =
      markovRangeIdempotent P G := by
  exact regularIdempotent_idempotent hG

/-- Idempotence of the complementary group-inverse projection. -/
theorem markovRangeComplement_idempotent {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    (1 - markovRangeIdempotent P G) *
      (1 - markovRangeIdempotent P G) = 1 - markovRangeIdempotent P G := by
  have hE := markovRangeIdempotent_idempotent P G hG
  change ((1 - P) * G) * ((1 - P) * G) = (1 - P) * G at hE
  change (1 - ((1 - P) * G)) * (1 - ((1 - P) * G)) =
    1 - ((1 - P) * G)
  calc
    _ = 1 - ((1 - P) * G) - ((1 - P) * G) +
        (((1 - P) * G) * ((1 - P) * G)) := by noncomm_ring
    _ = 1 - ((1 - P) * G) := by rw [hE]; noncomm_ring

/-- The range and complementary projections sum to the identity. -/
theorem markovRange_kernelComplement_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P G : Matrix ι ι ℝ) :
    markovRangeIdempotent P G + (1 - markovRangeIdempotent P G) = 1 := by
  noncomm_ring

/-- The two Markov projections annihilate in the range-then-complement order. -/
theorem markovRange_mul_kernelComplement_eq_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    markovRangeIdempotent P G * (1 - markovRangeIdempotent P G) = 0 := by
  have hE := markovRangeIdempotent_idempotent P G hG
  change ((1 - P) * G) * ((1 - P) * G) = (1 - P) * G at hE
  change ((1 - P) * G) * (1 - ((1 - P) * G)) = 0
  calc
    _ = ((1 - P) * G) - (((1 - P) * G) * ((1 - P) * G)) := by noncomm_ring
    _ = 0 := by rw [hE]; noncomm_ring

/-- The two Markov projections annihilate in the complement-then-range order. -/
theorem markovKernelComplement_mul_range_eq_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P G : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    (1 - markovRangeIdempotent P G) * markovRangeIdempotent P G = 0 := by
  have hE := markovRangeIdempotent_idempotent P G hG
  change ((1 - P) * G) * ((1 - P) * G) = (1 - P) * G at hE
  change (1 - ((1 - P) * G)) * ((1 - P) * G) = 0
  calc
    _ = ((1 - P) * G) - (((1 - P) * G) * ((1 - P) * G)) := by noncomm_ring
    _ = 0 := by rw [hE]; noncomm_ring

/-- Petz compression by the Markov range projection is idempotent on the full
noncommutative matrix carrier. -/
theorem markovRange_petzRecovery_idempotent {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P G X : Matrix ι ι ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    petzRecovery (markovRangeIdempotent P G)
      (petzRecovery (markovRangeIdempotent P G) X) =
        petzRecovery (markovRangeIdempotent P G) X := by
  exact petz_recovery_idempotent (markovRangeIdempotent P G)
    (markovRangeIdempotent_idempotent P G hG) X

/-- On the full matrix carrier, left multiplication by the Markov range
idempotent has exactly the same range as left multiplication by `1 - P`.
This transports the column-observable range theorem to matrix-valued forces. -/
theorem markovRangeIdempotent_leftRange_eq_laplacian_leftRange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P G : Matrix ι ι ℝ) (hG : IsGroupInverse (1 - P) G) :
    (mulLeftLinearMap ι ℝ (markovRangeIdempotent P G)).range =
      (markovLeftOnsager P).range := by
  let a : Module.End ℝ (Matrix ι ι ℝ) := mulLeftLinearMap ι ℝ (1 - P)
  let g : Module.End ℝ (Matrix ι ι ℝ) := mulLeftLinearMap ι ℝ G
  have hLift : IsGroupInverse a g := by
    simpa [a, g, markovLeftOnsager] using
      mulLeftLinearMap_groupInverse (1 - P) G hG
  have hmul : a * g = mulLeftLinearMap ι ℝ (markovRangeIdempotent P G) := by
    simp [a, g, markovRangeIdempotent, mulLeftLinearMap_mul,
      Module.End.mul_eq_comp]
  rw [← hmul]
  exact groupInverse_regularProjector_range a g hLift

/-- Every finite row-stochastic operator admits the algebraic Markov range
projection used by the preceding Petz compression theorems. -/
theorem exists_stochastic_markovRangeIdempotent {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : Matrix ι ι ℝ, IsGroupInverse (1 - P) G := by
  obtain ⟨D, hD⟩ :=
    InfoGeometry.QuantumContext.MarkovDrazin.exists_stochastic_laplacian_groupInverse P hP
  exact InfoGeometry.QuantumContext.MarkovDrazin.matrix_groupInverse_of_linear_groupInverse
    (1 - P) D (by simpa using hD)

end InfoGeometry.QuantumContext
