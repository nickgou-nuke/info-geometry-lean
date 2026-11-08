/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.AttentionGNSBridge
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
import InfoGeometry.QuantumContext.MarkovPetzRatioWeightedAdjoint

/-!
# Attention KMS Modular Operator, Ratio-Weighted Pairing, and Group-Inverse Range Compression

This module bridges the finite-matrix GNS and KMS attention state infrastructure
(`MatrixGNS`, `AttentionKMSState`, `ColimitAttentionTomitaFlow`) with the stationary-weighted
Markov adjoint and Drazin/group-inverse range compression (`MarkovWeightedMatrixTrace`,
`MarkovRangeOrthogonalProjection`, `MarkovPetzRatioWeightedAdjoint`):

1. **Archetype I — Unification of `weightedMatrixPairing`, `gnsInner`, and `attentionState`**:
   - Proves the exact transpose duality between `MarkovDrazin.weightedMatrixPairing π X Y = Tr(diag(π) X Yᵀ)`
     and `MatrixGNS.gnsInner (diag(π)) A B = Tr(diag(π) Aᵀ B)`:
     `weightedMatrixPairing π X Y = gnsInner (diag(π)) Xᵀ Yᵀ`.
   - Specializes this duality to `attentionDensityMatrix logits β` and `attentionState`.

2. **Archetype II — `ratioWeightedMatrixPairing` as the Attention Modular KMS Pairing**:
   - Identifies `MarkovDrazin.ratioWeightedMatrixPairing (softmaxWeight logits β) X Y` with the
     trace pairing `Tr(Xᵀ · attentionModularDelta logits β Y)` against the Tomita modular
     operator `Δ_ρ(Y) = ρ Y ρ⁻¹`.
   - Expands the pairing in terms of the Boltzmann weight ratios `exp(β (logits_i - logits_j))`
     and proves positive semi-definiteness `0 ≤ ratioWeightedMatrixPairing (softmaxWeight logits β) X X`.

3. **Archetype III — Boltzmann-Weighted Adjoint Transpose & Modular Adjointness**:
   - Proves an algebraic diagonal-conjugation identity for any weight vector `π`;
     the GNS modular interpretation is used for the strictly positive softmax weights.
   - Deduces the entrywise Boltzmann formula for `weightedAdjoint (softmaxWeight logits β) M`
     and characterizes `DetailedBalance (softmaxWeight logits β) P` by the modular symmetry
     condition `attentionModularDelta logits β P = Pᵀ`.

4. **Archetype IV — Detailed-Balance Group-Inverse Range Compression on the Attention KMS State**:
   - Instantiates self-adjointness and complement orthogonality of `markovRangeIdempotent P G`
     in the softmax-weighted Frobenius pairing, and two-sided compression self-adjointness
     with respect to `attentionModularDelta logits β`.
   - Constructs the non-trivial rank-1 stationary softmax Markov transition matrix
     `attentionStationaryMatrix logits β` and its complementary idempotent group inverse
     `1 - attentionStationaryMatrix logits β`, proving that the resulting range idempotent on
     `Fin 2` is neither `0` nor `1` (`E ≠ 0` and `E ≠ 1`) and satisfies two-sided modular
     compression self-adjointness.

## Scope Note

This module formalizes:
1. finite-dimensional diagonal KMS modular operators (`attentionModularDelta`),
2. the stationary-weighted matrix adjoint (`Probability.weightedAdjoint`) and its
   exact transpose identity with `MatrixGNS.modularDelta`,
3. the Boltzmann ratio-weighted Frobenius pairing (`MarkovDrazin.ratioWeightedMatrixPairing`)
   as the KMS modular trace pairing `Tr(Xᵀ · attentionModularDelta logits β Y)`, and
4. two-sided Drazin/group-inverse range compression (`markovRangeIdempotent P G`) under
   detailed balance.

It does not claim or construct a general completely positive trace-preserving (CPTP) quantum
channel or the square-root CPTP Petz recovery superoperator
`R_{σ,N}(X) = σ^{1/2} N†(N(σ)^{-1/2} X N(σ)^{-1/2}) σ^{1/2}`.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionKMSPetzRecoveryBridge

open BigOperators Matrix
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionGNSBridge
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

variable {ι : Type*}

/-! ### Archetype I: Unification of `weightedMatrixPairing`, `gnsInner`, and `AttentionKMSState` -/

/-- Exact transpose duality between `MarkovDrazin.weightedMatrixPairing` and `MatrixGNS.gnsInner`:
`weightedMatrixPairing π X Y = Tr(diag(π) X Yᵀ) = gnsInner (diag(π)) Xᵀ Yᵀ`. -/
theorem weightedMatrixPairing_eq_gnsInner_transpose [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (X Y : Matrix ι ι ℝ) :
    MarkovDrazin.weightedMatrixPairing π X Y =
      MatrixGNS.gnsInner (Matrix.diagonal π) Xᵀ Yᵀ := by
  rw [MarkovDrazin.weightedMatrixPairing_eq_trace_weighted_product]
  dsimp [MarkovDrazin.weightDiagonalOperator, MatrixGNS.gnsInner]
  rw [Matrix.transpose_transpose]

/-- Inverse transpose duality expressing the diagonal GNS inner product in terms of
`MarkovDrazin.weightedMatrixPairing`. -/
theorem gnsInner_diagonal_eq_weightedMatrixPairing_transpose [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (A B : Matrix ι ι ℝ) :
    MatrixGNS.gnsInner (Matrix.diagonal π) A B =
      MarkovDrazin.weightedMatrixPairing π Aᵀ Bᵀ := by
  rw [weightedMatrixPairing_eq_gnsInner_transpose, Matrix.transpose_transpose,
    Matrix.transpose_transpose]

/-- The GNS inner product associated with `attentionDensityMatrix logits β` coincides with
`MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β)` on the transposed arguments. -/
theorem attentionGNSInner_eq_weightedMatrixPairing_transpose [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (A B : Matrix ι ι ℝ) :
    MatrixGNS.gnsInner (attentionDensityMatrix logits β) A B =
      MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) Aᵀ Bᵀ := by
  dsimp [attentionDensityMatrix]
  exact gnsInner_diagonal_eq_weightedMatrixPairing_transpose (softmaxWeight logits β) A B

/-- The quadratic evaluation `attentionState logits β (Bᵀ * B)` equals the self-pairing
of `Bᵀ` under `MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β)`. -/
theorem attentionState_quadratic_eq_weightedMatrixPairing [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (B : Matrix ι ι ℝ) :
    attentionState logits β (Bᵀ * B) =
      MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) Bᵀ Bᵀ := by
  rw [attentionState_quadratic_eq_gnsInner]
  exact attentionGNSInner_eq_weightedMatrixPairing_transpose logits β B B

/-! ### Archetype II: `ratioWeightedMatrixPairing` as the Attention Modular KMS Pairing -/

private theorem weight_mul_self_nonneg (a x : ℝ) (ha : 0 ≤ a) :
    0 ≤ a * x * x := by
  have hsq : 0 ≤ x * x := mul_self_nonneg x
  have hmul : 0 ≤ a * (x * x) := mul_nonneg ha hsq
  simpa only [mul_assoc] using hmul

/-- For `π = softmaxWeight logits β`, the Boltzmann ratio-weighted matrix pairing
`ratioWeightedMatrixPairing (softmaxWeight logits β) X Y` is identically the Hilbert–Schmidt
trace pairing of `X` against the KMS modular operator `attentionModularDelta logits β Y`. -/
theorem ratioWeightedMatrixPairing_softmax_eq_trace_modularDelta
    [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (X Y : Matrix ι ι ℝ) :
    MarkovDrazin.ratioWeightedMatrixPairing (softmaxWeight logits β) X Y =
      Matrix.trace (Xᵀ * attentionModularDelta logits β Y) := by
  dsimp [MarkovDrazin.ratioWeightedMatrixPairing, attentionModularDelta,
    MatrixGNS.modularDelta]
  simp only [Matrix.mul_assoc]

/-- Entrywise expansion of `ratioWeightedMatrixPairing (softmaxWeight logits β) X Y` in terms
of the Boltzmann weight ratios `exp(β (logits_i - logits_j))`. -/
theorem ratioWeightedMatrixPairing_softmax_eq_sum_exp
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (X Y : Matrix ι ι ℝ) :
    MarkovDrazin.ratioWeightedMatrixPairing (softmaxWeight logits β) X Y =
      ∑ i, ∑ j, Real.exp (β * (logits i - logits j)) * X i j * Y i j := by
  rw [MarkovDrazin.ratioWeightedMatrixPairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [softmaxWeight_div_eq_exp_sub logits β i j]

/-- Positive semi-definiteness of the softmax ratio-weighted matrix pairing on any matrix `X`. -/
theorem ratioWeightedMatrixPairing_symm_self_nonneg
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (X : Matrix ι ι ℝ) :
    0 ≤ MarkovDrazin.ratioWeightedMatrixPairing (softmaxWeight logits β) X X := by
  rw [ratioWeightedMatrixPairing_softmax_eq_sum_exp]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact weight_mul_self_nonneg
    (Real.exp (β * (logits i - logits j))) (X i j) (le_of_lt (Real.exp_pos _))

/-! ### Archetype III: Boltzmann-Weighted Adjoint Transpose & Modular Adjointness -/

private theorem inv_mul_mul_eq_mul_mul_inv (a b x : ℝ) :
    b⁻¹ * x * a = a * x * b⁻¹ := by
  ring

/-- For any weight vector `π`, the transpose of `weightedAdjoint π M` equals the
algebraically defined diagonal-conjugation map `modularDelta π M = diag(π) M diag(π⁻¹)`.
This identity itself assumes no faithfulness; its GNS modular interpretation is used
below for strictly positive softmax weights. -/
theorem weightedAdjoint_transpose_eq_modularDelta [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (M : Matrix ι ι ℝ) :
    (InfoGeometry.Probability.weightedAdjoint π M)ᵀ =
      MatrixGNS.modularDelta π M := by
  ext i j
  dsimp [InfoGeometry.Probability.weightedAdjoint, MatrixGNS.modularDelta,
    Matrix.transpose_apply]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact inv_mul_mul_eq_mul_mul_inv (π i) (π j) (M i j)

/-- Under `softmaxWeight logits β`, the transpose of `weightedAdjoint (softmaxWeight logits β) M`
is identically the attention modular operator `attentionModularDelta logits β M`. -/
theorem weightedAdjoint_softmax_transpose_eq_modularDelta
    [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (M : Matrix ι ι ℝ) :
    (InfoGeometry.Probability.weightedAdjoint (softmaxWeight logits β) M)ᵀ =
      attentionModularDelta logits β M := by
  dsimp [attentionModularDelta]
  exact weightedAdjoint_transpose_eq_modularDelta (softmaxWeight logits β) M

/-- Entrywise Boltzmann ratio formula for the stationary-weighted adjoint under
`softmaxWeight logits β`: the `(i, j)` entry of `weightedAdjoint (softmaxWeight logits β) M`
is `exp(β (logits_j - logits_i)) * M j i`. -/
theorem weightedAdjoint_softmax_apply_eq_exp_sub
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (M : Matrix ι ι ℝ) (i j : ι) :
    InfoGeometry.Probability.weightedAdjoint (softmaxWeight logits β) M i j =
      Real.exp (β * (logits j - logits i)) * M j i := by
  change (InfoGeometry.Probability.weightedAdjoint (softmaxWeight logits β) M)ᵀ j i =
    Real.exp (β * (logits j - logits i)) * M j i
  rw [weightedAdjoint_softmax_transpose_eq_modularDelta]
  exact attentionModularDelta_apply_eq_exp_sub logits β M j i

/-- Detailed balance of `P` with respect to `softmaxWeight logits β` holds if and only if
the attention modular operator maps `P` to its transpose: `attentionModularDelta logits β P = Pᵀ`. -/
theorem detailedBalance_softmax_iff_modularDelta_eq_transpose
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (P : Matrix ι ι ℝ) :
    InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β) P ↔
      attentionModularDelta logits β P = Pᵀ := by
  have hπ : ∀ i, softmaxWeight logits β i ≠ 0 :=
    fun i => ne_of_gt (softmaxWeight_pos logits β i)
  rw [InfoGeometry.Probability.detailedBalance_iff_weightedAdjoint_eq
    (softmaxWeight logits β) P hπ]
  rw [← weightedAdjoint_softmax_transpose_eq_modularDelta]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← Matrix.transpose_transpose
      (InfoGeometry.Probability.weightedAdjoint (softmaxWeight logits β) P),
      h, Matrix.transpose_transpose]

/-! ### Archetype IV: Detailed-Balance Group-Inverse Range Compression on the Attention KMS State -/

/-- Under softmax detailed balance and a supplied group inverse `G` of `1 - P`,
left multiplication by `markovRangeIdempotent P G` is self-adjoint in the softmax-weighted
Frobenius pairing. -/
theorem attention_markovRange_selfAdjoint
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (P G : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β) P)
    (X Y : Matrix ι ι ℝ) :
    MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β)
        (InfoGeometry.QuantumContext.markovRangeIdempotent P G * X) Y =
      MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β) X
        (InfoGeometry.QuantumContext.markovRangeIdempotent P G * Y) :=
  MarkovDrazin.weightedMatrixPairing_markovRange_selfAdjoint P G
    (softmaxWeight logits β) hG hDB
    (fun i => ne_of_gt (softmaxWeight_pos logits β i)) X Y

/-- Under softmax detailed balance and a supplied group inverse `G` of `1 - P`,
the range projection `markovRangeIdempotent P G` and its kernel complement
`1 - markovRangeIdempotent P G` are mutually orthogonal in the softmax-weighted pairing. -/
theorem attention_markovRange_complement_orthogonal
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (P G : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β) P)
    (X Y : Matrix ι ι ℝ) :
    MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β)
        (InfoGeometry.QuantumContext.markovRangeIdempotent P G * X)
        ((1 - InfoGeometry.QuantumContext.markovRangeIdempotent P G) * Y) = 0 ∧
      MarkovDrazin.weightedMatrixPairing (softmaxWeight logits β)
        ((1 - InfoGeometry.QuantumContext.markovRangeIdempotent P G) * X)
        (InfoGeometry.QuantumContext.markovRangeIdempotent P G * Y) = 0 :=
  MarkovDrazin.weightedMatrixPairing_markovRange_complement_orthogonal P G
    (softmaxWeight logits β) hG hDB
    (fun i => ne_of_gt (softmaxWeight_pos logits β i)) X Y

/-- **Attention KMS Modular Self-Adjointness of Two-Sided Range Compression**:
Under softmax detailed balance and a supplied group inverse `G` of `1 - P`, two-sided
compression `X ↦ E X E` by `E = markovRangeIdempotent P G` is self-adjoint in the
modular-operator trace pairing `Tr(Xᵀ · attentionModularDelta logits β Y)`. -/
theorem attention_markovCompression_modularDelta_selfAdjoint
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) (P G : Matrix ι ι ℝ)
    (hG : InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse (1 - P) G)
    (hDB : InfoGeometry.Probability.DetailedBalance (softmaxWeight logits β) P)
    (X Y : Matrix ι ι ℝ) :
    Matrix.trace
        ((InfoGeometry.QuantumContext.markovRangeIdempotent P G * X *
          InfoGeometry.QuantumContext.markovRangeIdempotent P G)ᵀ *
          attentionModularDelta logits β Y) =
      Matrix.trace
        (Xᵀ * attentionModularDelta logits β
          (InfoGeometry.QuantumContext.markovRangeIdempotent P G * Y *
            InfoGeometry.QuantumContext.markovRangeIdempotent P G)) := by
  rw [← ratioWeightedMatrixPairing_softmax_eq_trace_modularDelta,
    ← ratioWeightedMatrixPairing_softmax_eq_trace_modularDelta]
  exact MarkovDrazin.ratioWeightedMatrixPairing_markovCompression_selfAdjoint P G
    (softmaxWeight logits β) hG hDB (softmaxWeight_pos logits β) X Y

/-! ### Non-Trivial Rank-1 Stationary Softmax Markov Transition Matrix & Range Compression -/

private theorem mul_sub_mul_comm_eq_zero (a b : ℝ) :
    a * b - b * a = 0 := by
  ring

/-- The rank-1 stationary transition matrix associated with weight vector `π`,
whose `(i, j)` entry is `π j` for every row `i`. -/
def stationaryTransitionMatrix (π : ι → ℝ) : Matrix ι ι ℝ :=
  fun _ j => π j

/-- The rank-1 stationary transition matrix `stationaryTransitionMatrix π` satisfies
exact detailed balance with respect to `π`: `π_i π_j - π_j π_i = 0`. -/
theorem stationaryTransitionMatrix_detailedBalance [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) :
    InfoGeometry.Probability.DetailedBalance π (stationaryTransitionMatrix π) := by
  ext i j
  rw [InfoGeometry.Probability.detailedBalanceResidual_apply]
  dsimp [InfoGeometry.Probability.stationaryEdgeCurrent, stationaryTransitionMatrix,
    Matrix.zero_apply]
  exact mul_sub_mul_comm_eq_zero (π i) (π j)

/-- When `∑ i, π i = 1`, the rank-1 stationary transition matrix is idempotent: `P² = P`. -/
theorem stationaryTransitionMatrix_mul_self [Fintype ι]
    (π : ι → ℝ) (hπ : ∑ i, π i = 1) :
    stationaryTransitionMatrix π * stationaryTransitionMatrix π =
      stationaryTransitionMatrix π := by
  ext i j
  dsimp [stationaryTransitionMatrix, Matrix.mul_apply]
  rw [← Finset.sum_mul, hπ, one_mul]

/-- When `∑ i, π i = 1`, the complementary Laplacian `1 - stationaryTransitionMatrix π`
is idempotent: `(1 - P)² = 1 - P`. -/
theorem one_sub_stationaryTransitionMatrix_idem [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (hπ : ∑ i, π i = 1) :
    (1 - stationaryTransitionMatrix π) * (1 - stationaryTransitionMatrix π) =
      1 - stationaryTransitionMatrix π := by
  rw [mul_sub, mul_one, sub_mul, one_mul,
    stationaryTransitionMatrix_mul_self π hπ, sub_self, sub_zero]

/-- Because `1 - stationaryTransitionMatrix π` is idempotent when `∑ i, π i = 1`,
it is its own Hartwig/Drazin group inverse. -/
theorem isGroupInverse_one_sub_stationaryTransitionMatrix [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (hπ : ∑ i, π i = 1) :
    InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
      (1 - stationaryTransitionMatrix π) (1 - stationaryTransitionMatrix π) := by
  have hidem := one_sub_stationaryTransitionMatrix_idem π hπ
  refine ⟨?_, ?_, rfl⟩
  · rw [hidem, hidem]
  · rw [hidem, hidem]

/-- The range idempotent `markovRangeIdempotent P (1 - P)` for `P = stationaryTransitionMatrix π`
equals the complementary projection `1 - stationaryTransitionMatrix π`. -/
theorem markovRangeIdempotent_stationaryTransitionMatrix_eq [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (hπ : ∑ i, π i = 1) :
    InfoGeometry.QuantumContext.markovRangeIdempotent
        (stationaryTransitionMatrix π) (1 - stationaryTransitionMatrix π) =
      1 - stationaryTransitionMatrix π := by
  change (1 - stationaryTransitionMatrix π) * (1 - stationaryTransitionMatrix π) =
    1 - stationaryTransitionMatrix π
  exact one_sub_stationaryTransitionMatrix_idem π hπ

/-- The rank-1 stationary softmax Markov transition matrix `P_{i,j} = softmaxWeight logits β j`. -/
def attentionStationaryMatrix [Fintype ι] (logits : ι → ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  stationaryTransitionMatrix (softmaxWeight logits β)

/-- The exact group inverse `G = 1 - attentionStationaryMatrix logits β` of the
stationary softmax Laplacian `1 - attentionStationaryMatrix logits β`. -/
def attentionStationaryGroupInv [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) : Matrix ι ι ℝ :=
  1 - attentionStationaryMatrix logits β

/-- Group-inverse certificate for `1 - attentionStationaryMatrix logits β`. -/
theorem attentionStationary_isGroupInverse [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
      (1 - attentionStationaryMatrix logits β)
      (attentionStationaryGroupInv logits β) :=
  isGroupInverse_one_sub_stationaryTransitionMatrix
    (softmaxWeight logits β) (softmaxWeight_sum_one logits β)

/-- Detailed-balance certificate for `attentionStationaryMatrix logits β`. -/
theorem attentionStationary_detailedBalance [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β : ℝ) :
    InfoGeometry.Probability.DetailedBalance
      (softmaxWeight logits β) (attentionStationaryMatrix logits β) :=
  stationaryTransitionMatrix_detailedBalance (softmaxWeight logits β)

/-- The range idempotent associated with `attentionStationaryMatrix logits β` and
`attentionStationaryGroupInv logits β` is `1 - attentionStationaryMatrix logits β`. -/
theorem attentionStationary_rangeIdempotent_eq [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    InfoGeometry.QuantumContext.markovRangeIdempotent
        (attentionStationaryMatrix logits β)
        (attentionStationaryGroupInv logits β) =
      1 - attentionStationaryMatrix logits β :=
  markovRangeIdempotent_stationaryTransitionMatrix_eq
    (softmaxWeight logits β) (softmaxWeight_sum_one logits β)

/-- **Non-Trivial Stationary Softmax Range Compression Modular Self-Adjointness**:
Two-sided compression by the codimension-1 mean-zero range projection of
`attentionStationaryMatrix logits β` is self-adjoint in the KMS modular trace pairing
`Tr(Xᵀ · attentionModularDelta logits β Y)`. -/
theorem attentionStationary_markovCompression_modularDelta_selfAdjoint
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (X Y : Matrix ι ι ℝ) :
    Matrix.trace
        ((InfoGeometry.QuantumContext.markovRangeIdempotent
          (attentionStationaryMatrix logits β)
          (attentionStationaryGroupInv logits β) * X *
          InfoGeometry.QuantumContext.markovRangeIdempotent
            (attentionStationaryMatrix logits β)
            (attentionStationaryGroupInv logits β))ᵀ *
          attentionModularDelta logits β Y) =
      Matrix.trace
        (Xᵀ * attentionModularDelta logits β
          (InfoGeometry.QuantumContext.markovRangeIdempotent
            (attentionStationaryMatrix logits β)
            (attentionStationaryGroupInv logits β) * Y *
            InfoGeometry.QuantumContext.markovRangeIdempotent
              (attentionStationaryMatrix logits β)
              (attentionStationaryGroupInv logits β))) :=
  attention_markovCompression_modularDelta_selfAdjoint logits β
    (attentionStationaryMatrix logits β)
    (attentionStationaryGroupInv logits β)
    (attentionStationary_isGroupInverse logits β)
    (attentionStationary_detailedBalance logits β) X Y

/-- Canonical two-token logit vector `(1, 0)` on `Fin 2`. -/
def canonicalLogits : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else 0

/-- Elementary off-diagonal matrix unit `E_{0,1}` on `Fin 2`. -/
def petzMatE01 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- Elementary off-diagonal matrix unit `E_{1,0}` on `Fin 2`. -/
def petzMatE10 : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`:
`petzMatE01 * petzMatE10 ≠ petzMatE10 * petzMatE01`. -/
theorem petzMatE01_mul_petzMatE10_ne :
    petzMatE01 * petzMatE10 ≠ petzMatE10 * petzMatE01 := by
  intro h
  have h00 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  dsimp [petzMatE01, petzMatE10, Matrix.mul_apply] at h00
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h00
  norm_num at h00

/-- Non-trivial Boltzmann off-diagonal modular scaling on the two-token witness `petzMatE01`:
`attentionModularDelta canonicalLogits β petzMatE01 0 1 = Real.exp β`. -/
theorem attentionModularDelta_canonicalLogits_petzMatE01 (β : ℝ) :
    attentionModularDelta canonicalLogits β petzMatE01 0 1 = Real.exp β := by
  rw [attentionModularDelta_apply_eq_exp_sub]
  have h0 : canonicalLogits 0 = 1 := rfl
  have h1 : canonicalLogits 1 = 0 := rfl
  have he : petzMatE01 0 1 = 1 := rfl
  rw [h0, h1, he, sub_zero, mul_one, mul_one]

/-- Off-diagonal entry `(0, 1)` of the stationary range idempotent on `Fin 2` equals
`- softmaxWeight logits β 1`. -/
theorem attentionStationary_rangeIdempotent_apply_zero_one
    (logits : Fin 2 → ℝ) (β : ℝ) :
    InfoGeometry.QuantumContext.markovRangeIdempotent
        (attentionStationaryMatrix logits β)
        (attentionStationaryGroupInv logits β) 0 1 =
      -softmaxWeight logits β 1 := by
  rw [attentionStationary_rangeIdempotent_eq]
  dsimp [attentionStationaryMatrix, stationaryTransitionMatrix]
  have h01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
    simp
  rw [h01, zero_sub]

/-- On `Fin 2`, the stationary range idempotent is non-zero (`E ≠ 0`) because its
off-diagonal `(0, 1)` entry is `- softmaxWeight logits β 1 ≠ 0`. -/
theorem attentionStationary_rangeIdempotent_ne_zero
    (logits : Fin 2 → ℝ) (β : ℝ) :
    InfoGeometry.QuantumContext.markovRangeIdempotent
        (attentionStationaryMatrix logits β)
        (attentionStationaryGroupInv logits β) ≠ 0 := by
  intro h
  have h01 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  rw [attentionStationary_rangeIdempotent_apply_zero_one, Matrix.zero_apply] at h01
  exact neg_ne_zero.mpr (ne_of_gt (softmaxWeight_pos logits β 1)) h01

/-- On `Fin 2`, the stationary range idempotent is not the identity matrix (`E ≠ 1`)
because its off-diagonal `(0, 1)` entry is `- softmaxWeight logits β 1 ≠ 0`, whereas `1_{0,1} = 0`. -/
theorem attentionStationary_rangeIdempotent_ne_one
    (logits : Fin 2 → ℝ) (β : ℝ) :
    InfoGeometry.QuantumContext.markovRangeIdempotent
        (attentionStationaryMatrix logits β)
        (attentionStationaryGroupInv logits β) ≠ 1 := by
  intro h
  have h01 := congr_arg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  have hone01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
    simp
  rw [attentionStationary_rangeIdempotent_apply_zero_one, hone01] at h01
  exact neg_ne_zero.mpr (ne_of_gt (softmaxWeight_pos logits β 1)) h01

end InfoGeometry.QuantumContext.AttentionKMSPetzRecoveryBridge

end
