/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ReplacementStateChannel

/-!
# Uniform states in orthogonal matrix blocks

## Overview

For a finite family of orthogonal star projections, the map constructed here
keeps each block's trace and replaces its contents by a scalar multiple of its
projection. Inputs are arbitrary full complex matrices; they need not commute
with any projection. Zero projections are allowed and contribute zero.

The map preserves positive semidefiniteness, is completely positive for every
finite ancillary index type, preserves the trace for a complete family, and
is an idempotent projection onto the span of the macro-projectors.

This operator construction supplies the coarse state used in observational
entropy. It asserts neither a matrix-logarithm formula nor an entropy
inequality or monotonicity along unitary time evolution.

## Key results

- `blockUniformChannel_readout`: every macro-projector readout is preserved.
- `blockUniformChannel_fixed_iff`: fixed matrices are exactly the block-scalar
  sums in the span of the macro-projectors.
- `blockUniformChannel_completely_positive`: positivity at every finite
  ancillary matrix size, proved from compression and replacement channels.

## Table of contents

1. Actual matrix channel and positive macro readouts.
2. Trace, fixed matrices, and density preservation.
3. Finite ancillary amplification and complete positivity.

## References

The existing Kraus amplification and replacement-channel owners supply the
operator structures. The observational-entropy interpretation follows
Strasberg and Winter, PRX Quantum 2, 030202 (2021); this file constructs the
coarse state and does not formalize that paper's entropy comparisons.
-/

noncomputable section

namespace InfoGeometry.Quantum.ProjectiveCoarseGraining

open Matrix
open InfoGeometry.Quantum.KrausAmplification
open InfoGeometry.Quantum.ReplacementStateChannel
open scoped ComplexOrder MatrixOrder

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

/-- The complex-linear map that uniformly fills each measured block. -/
def blockUniformChannel (P : ι → Mat) : Mat →ₗ[ℂ] Mat where
  toFun X := ∑ i, (Matrix.trace (P i * X) / Matrix.trace (P i)) • P i
  map_add' X Y := by
    simp [mul_add, Matrix.trace_add, add_div, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [Matrix.trace_smul, smul_smul, mul_div_assoc, Finset.smul_sum]

@[simp] theorem blockUniformChannel_apply (P : ι → Mat) (X : Mat) :
    blockUniformChannel P X =
      ∑ i, (Matrix.trace (P i * X) / Matrix.trace (P i)) • P i := rfl

/-- Cyclicity turns a projection readout into the trace of its compression. -/
theorem trace_projection_compression (P X : Mat) (hP : IsIdempotentElem P) :
    Matrix.trace (P * X * P) = Matrix.trace (P * X) := by
  rw [Matrix.trace_mul_cycle, hP]

/-- Every macro readout is nonnegative on an arbitrary positive input. -/
theorem trace_projection_mul_nonneg (P X : Mat) (hP : IsStarProjection P)
    (hX : X.PosSemidef) : 0 ≤ Matrix.trace (P * X) := by
  have hc := hX.mul_mul_conjTranspose_same P
  have hs : Pᴴ = P := hP.isSelfAdjoint.star_eq
  rw [hs] at hc
  rw [← trace_projection_compression P X hP.isIdempotentElem]
  exact hc.trace_nonneg

/-- The macro readouts sum to the actual full matrix trace. -/
theorem sum_trace_projection_mul (P : ι → Mat) (hSum : ∑ i, P i = 1) (X : Mat) :
    (∑ i, Matrix.trace (P i * X)) = Matrix.trace X := by
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hSum, one_mul]

/-- Uniform replacement in every block preserves positive semidefiniteness. -/
theorem blockUniformChannel_posSemidef (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i)) (X : Mat) (hX : X.PosSemidef) :
    (blockUniformChannel P X).PosSemidef := by
  rw [blockUniformChannel_apply]
  apply Matrix.posSemidef_sum
  intro i _
  exact (hP i).nonneg.posSemidef.smul
    (div_nonneg (trace_projection_mul_nonneg (P i) X (hP i) hX)
      (hP i).nonneg.posSemidef.trace_nonneg)

/-- A zero-volume projection is zero, so empty blocks require no division
hypothesis in trace preservation. -/
theorem blockUniformChannel_trace (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i)) (hSum : ∑ i, P i = 1) (X : Mat) :
    Matrix.trace (blockUniformChannel P X) = Matrix.trace X := by
  rw [blockUniformChannel_apply, Matrix.trace_sum]
  calc
    (∑ i, Matrix.trace ((Matrix.trace (P i * X) / Matrix.trace (P i)) • P i)) =
        ∑ i, Matrix.trace (P i * X) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz : P i = 0
      · simp [hz]
      · rw [Matrix.trace_smul]
        exact div_mul_cancel₀ _
          (fun ht => hz ((hP i).nonneg.posSemidef.trace_eq_zero_iff.mp ht))
    _ = Matrix.trace X := sum_trace_projection_mul P hSum X

/-- The complete family fixes the identity, including when some blocks vanish. -/
theorem blockUniformChannel_one (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i)) (hSum : ∑ i, P i = 1) :
    blockUniformChannel P (1 : Mat) = 1 := by
  calc
    blockUniformChannel P (1 : Mat) = ∑ i, P i := by
      rw [blockUniformChannel_apply]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz : P i = 0
      · simp [hz]
      · have ht : Matrix.trace (P i) ≠ 0 :=
          fun h => hz ((hP i).nonneg.posSemidef.trace_eq_zero_iff.mp h)
        simp [ht]
    _ = 1 := hSum

/-- The channel preserves every macro-projector readout exactly. -/
theorem blockUniformChannel_readout (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (X : Mat) (i : ι) :
    Matrix.trace (P i * blockUniformChannel P X) = Matrix.trace (P i * X) := by
  classical
  by_cases hz : P i = 0
  · simp [hz]
  have ht : Matrix.trace (P i) ≠ 0 :=
    fun h => hz ((hP i).nonneg.posSemidef.trace_eq_zero_iff.mp h)
  simp only [blockUniformChannel_apply, Finset.mul_sum, Matrix.trace_sum,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [(hP i).isIdempotentElem]
    exact div_mul_cancel₀ _ ht
  · intro j _ hji
    rw [hOrth i j (Ne.symm hji), Matrix.trace_zero, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Reapplying uniform replacement does not change the coarse matrix. -/
theorem blockUniformChannel_idempotent (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (X : Mat) :
    blockUniformChannel P (blockUniformChannel P X) = blockUniformChannel P X := by
  change (∑ i, (Matrix.trace (P i * blockUniformChannel P X) /
      Matrix.trace (P i)) • P i) =
    ∑ i, (Matrix.trace (P i * X) / Matrix.trace (P i)) • P i
  apply Finset.sum_congr rfl
  intro i _
  rw [blockUniformChannel_readout P hP hOrth X i]

/-- Each individual macro-projector is a fixed matrix. -/
theorem blockUniformChannel_projection (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (j : ι) :
    blockUniformChannel P (P j) = P j := by
  classical
  by_cases hz : P j = 0
  · rw [hz, map_zero]
  have ht : Matrix.trace (P j) ≠ 0 :=
    fun h => hz ((hP j).nonneg.posSemidef.trace_eq_zero_iff.mp h)
  rw [blockUniformChannel_apply, Finset.sum_eq_single j]
  · rw [(hP j).isIdempotentElem, div_self ht, one_smul]
  · intro i _ hij
    rw [hOrth i j hij, Matrix.trace_zero, zero_div, zero_smul]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- All block-scalar matrices are fixed by the actual linear map. -/
theorem blockUniformChannel_block_scalars (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (c : ι → ℂ) :
    blockUniformChannel P (∑ i, c i • P i) = ∑ i, c i • P i := by
  simp only [map_sum, map_smul, blockUniformChannel_projection P hP hOrth]

/-- The fixed matrices are exactly the span of the macro-projectors, expressed
as finite block-scalar sums without selecting a basis in any block. -/
theorem blockUniformChannel_fixed_iff (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (X : Mat) :
    blockUniformChannel P X = X ↔ ∃ c : ι → ℂ, X = ∑ i, c i • P i := by
  constructor
  · intro hX
    exact ⟨fun i => Matrix.trace (P i * X) / Matrix.trace (P i), hX.symm⟩
  · rintro ⟨c, rfl⟩
    exact blockUniformChannel_block_scalars P hP hOrth c

/-- Every block-scalar observable has the same expectation before and after
coarse graining. This is an operator trace identity, without a logarithm claim. -/
theorem blockUniformChannel_block_observable (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    (hOrth : ∀ i j, i ≠ j → P i * P j = 0) (c : ι → ℂ) (X : Mat) :
    Matrix.trace ((∑ i, c i • P i) * blockUniformChannel P X) =
      Matrix.trace ((∑ i, c i • P i) * X) := by
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [blockUniformChannel_readout P hP hOrth X i]

/-- Uniform replacement sends every density matrix to a density matrix. -/
theorem blockUniformChannel_is_density (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i)) (hSum : ∑ i, P i = 1)
    (X : Mat) (hX : X.PosSemidef) (hTrace : Matrix.trace X = 1) :
    (blockUniformChannel P X).PosSemidef ∧
      Matrix.trace (blockUniformChannel P X) = 1 :=
  ⟨blockUniformChannel_posSemidef P hP X hX,
    (blockUniformChannel_trace P hP hSum X).trans hTrace⟩

/-- At every ancillary size the channel is a sum of an actual matrix compression
followed by the existing replacement channel. -/
theorem amplification_blockUniformChannel (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Fin d) (r × Fin d) ℂ) :
    amplification (r := r) (blockUniformChannel P) X =
      ∑ k, amplification (r := r) (replacement ((Matrix.trace (P k))⁻¹ • P k))
        (blockK (r := r) (P k) * X * (blockK (r := r) (P k))ᴴ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [amplification_apply, blockUniformChannel_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hb : block (blockK (r := r) (P k) * X * (blockK (r := r) (P k))ᴴ) a b =
      P k * block X a b * star (P k) := by
    ext u v
    exact hblock (P k) X a b u v
  change ((Matrix.trace (P k * block X a b) / Matrix.trace (P k)) • P k) i j =
    (Matrix.trace (block
      (blockK (r := r) (P k) * X * (blockK (r := r) (P k))ᴴ) a b) •
        ((Matrix.trace (P k))⁻¹ • P k)) i j
  rw [hb, (hP k).isSelfAdjoint.star_eq,
    trace_projection_compression (P k) (block X a b) (hP k).isIdempotentElem]
  simp only [smul_smul, div_eq_mul_inv]

/-- Complete positivity for every finite ancillary index type follows from
compression positivity and the established replacement-channel theorem. -/
theorem blockUniformChannel_completely_positive (P : ι → Mat)
    (hP : ∀ i, IsStarProjection (P i))
    {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Fin d) (r × Fin d) ℂ) (hX : X.PosSemidef) :
    (amplification (r := r) (blockUniformChannel P) X).PosSemidef := by
  rw [amplification_blockUniformChannel P hP X]
  apply Matrix.posSemidef_sum
  intro i _
  apply replacement_completely_positive_all
  · exact (hP i).nonneg.posSemidef.smul
      (inv_nonneg.mpr (hP i).nonneg.posSemidef.trace_nonneg)
  · exact hX.mul_mul_conjTranspose_same (blockK (r := r) (P i))

end InfoGeometry.Quantum.ProjectiveCoarseGraining

end
