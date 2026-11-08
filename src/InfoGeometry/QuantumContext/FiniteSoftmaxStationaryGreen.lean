/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange
import InfoGeometry.QuantumContext.MarkovAttentionGreenReciprocity

/-!
# Stationary weights and Green reciprocity for finite softmax kernels

Every finite row-softmax kernel has a unique positive normalized stationary
row weight. For symmetric scores, the row partition functions give that weight
explicitly, detailed balance follows, and the group-inverse Green operator is
self-adjoint in the resulting weighted pairing.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

open Matrix
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The unique positive normalized stationary row weight of any finite
row-softmax attention matrix. -/
theorem existsUnique_softmax_stationary_row (scores : ι → ι → ℝ) :
    ∃! π : ι → ℝ,
      (∀ i, 0 < π i) ∧
      (∑ i, π i = 1) ∧
      (∀ j, ∑ i, π i * softmaxAttentionMatrix scores i j = π j) := by
  apply existsUnique_positive_normalized_stationary_row
    (softmaxAttentionMatrix scores)
    (softmaxAttentionMatrix_mem_rowStochastic scores)
  intro i j
  rw [softmaxAttentionMatrix_apply]
  exact softmaxAttentionKernel_pos scores i j

/-- Total mass of the row partition functions. -/
def softmaxPartitionMass (scores : ι → ι → ℝ) : ℝ :=
  ∑ i, queryPartitionFunction scores i

/-- Canonical stationary weight for symmetric scores: mass is proportional to
the row partition function. -/
def softmaxPartitionStationaryWeight (scores : ι → ι → ℝ) (i : ι) : ℝ :=
  queryPartitionFunction scores i / softmaxPartitionMass scores

omit [DecidableEq ι] in
theorem softmaxPartitionMass_pos (scores : ι → ι → ℝ) :
    0 < softmaxPartitionMass scores := by
  unfold softmaxPartitionMass
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (queryPartitionFunction_pos scores i)
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Finset.mem_univ _, queryPartitionFunction_pos scores i⟩

omit [DecidableEq ι] in
theorem softmaxPartitionStationaryWeight_pos
    (scores : ι → ι → ℝ) (i : ι) :
    0 < softmaxPartitionStationaryWeight scores i := by
  exact div_pos (queryPartitionFunction_pos scores i)
    (softmaxPartitionMass_pos scores)

omit [DecidableEq ι] in
theorem softmaxPartitionStationaryWeight_sum (scores : ι → ι → ℝ) :
    ∑ i, softmaxPartitionStationaryWeight scores i = 1 := by
  unfold softmaxPartitionStationaryWeight softmaxPartitionMass
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (by
    apply Finset.sum_pos'
    · intro i _
      exact le_of_lt (queryPartitionFunction_pos scores i)
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, Finset.mem_univ _, queryPartitionFunction_pos scores i⟩))

omit [DecidableEq ι] in
/-- Under symmetric scores, stationary mass times a transition entry is the
common Gibbs weight divided by total partition mass. -/
theorem softmaxPartitionStationaryWeight_mul_kernel
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i)
    (i j : ι) :
    softmaxPartitionStationaryWeight scores i * softmaxAttentionMatrix scores i j =
      gibbsCouplingWeight scores i j / softmaxPartitionMass scores := by
  unfold softmaxPartitionStationaryWeight softmaxAttentionMatrix
    softmaxAttentionKernel
  rw [div_mul_div_comm]
  unfold queryPartitionFunction softmaxPartitionMass
  simp only [gibbsCouplingWeight]
  rw [hsymm i j]
  field_simp [ne_of_gt (queryPartitionFunction_pos scores i),
    ne_of_gt (softmaxPartitionMass_pos scores)]

omit [DecidableEq ι] in
/-- Symmetric row-softmax scores have the explicit stationary distribution
proportional to their row partition functions. -/
theorem softmaxPartitionStationaryWeight_stationary
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i)
    (j : ι) :
    ∑ i, softmaxPartitionStationaryWeight scores i *
      softmaxAttentionMatrix scores i j = softmaxPartitionStationaryWeight scores j := by
  calc
    (∑ i, softmaxPartitionStationaryWeight scores i *
        softmaxAttentionMatrix scores i j) =
        ∑ i, softmaxPartitionStationaryWeight scores j *
          softmaxAttentionMatrix scores j i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              softmaxPartitionStationaryWeight scores i *
                  softmaxAttentionMatrix scores i j =
                gibbsCouplingWeight scores i j / softmaxPartitionMass scores :=
                  softmaxPartitionStationaryWeight_mul_kernel scores hsymm i j
              _ = gibbsCouplingWeight scores j i / softmaxPartitionMass scores := by
                unfold gibbsCouplingWeight
                rw [hsymm i j]
              _ = softmaxPartitionStationaryWeight scores j *
                  softmaxAttentionMatrix scores j i :=
                (softmaxPartitionStationaryWeight_mul_kernel scores hsymm j i).symm
    _ = softmaxPartitionStationaryWeight scores j := by
      rw [← Finset.mul_sum]
      have hrow : ∑ i, softmaxAttentionMatrix scores j i = 1 := by
        simpa only [softmaxAttentionMatrix_apply] using
          softmaxAttentionKernel_row_sum scores j
      rw [hrow, mul_one]

/-- Symmetric scores make the row-softmax transition matrix reversible with
respect to the partition-function stationary weight. -/
theorem softmaxPartitionStationaryWeight_detailedBalance
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i) :
    DetailedBalance (softmaxPartitionStationaryWeight scores)
      (softmaxAttentionMatrix scores) := by
  apply (detailedBalance_iff_all_edge_currents_zero _ _).2
  intro i j
  unfold stationaryEdgeCurrent
  calc
    softmaxPartitionStationaryWeight scores i * softmaxAttentionMatrix scores i j -
        softmaxPartitionStationaryWeight scores j * softmaxAttentionMatrix scores j i =
      gibbsCouplingWeight scores i j / softmaxPartitionMass scores -
        gibbsCouplingWeight scores j i / softmaxPartitionMass scores := by
          rw [softmaxPartitionStationaryWeight_mul_kernel scores hsymm i j,
            softmaxPartitionStationaryWeight_mul_kernel scores hsymm j i]
    _ = 0 := by
      unfold gibbsCouplingWeight
      rw [hsymm i j]
      ring

omit [DecidableEq ι] in
/-- The symmetric-score partition weight satisfies all three defining
conditions for a positive normalized stationary row distribution. -/
theorem softmaxPartitionStationaryWeight_is_stationary
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i) :
    (∀ i, 0 < softmaxPartitionStationaryWeight scores i) ∧
    (∑ i, softmaxPartitionStationaryWeight scores i = 1) ∧
    (∀ j, ∑ i, softmaxPartitionStationaryWeight scores i *
      softmaxAttentionMatrix scores i j = softmaxPartitionStationaryWeight scores j) := by
  exact ⟨softmaxPartitionStationaryWeight_pos scores,
    softmaxPartitionStationaryWeight_sum scores,
    softmaxPartitionStationaryWeight_stationary scores hsymm⟩

/-- For symmetric scores, every positive normalized stationary row weight is
the explicit partition-function weight. This identifies the closed formula
with the unique stationary row law, rather than merely showing it is one such
law. -/
theorem softmaxPartitionStationaryWeight_unique
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i)
    (π : ι → ℝ)
    (hπpos : ∀ i, 0 < π i)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * softmaxAttentionMatrix scores i j = π j) :
    π = softmaxPartitionStationaryWeight scores := by
  exact (existsUnique_softmax_stationary_row scores).unique
    ⟨hπpos, hπsum, hπstat⟩
    (softmaxPartitionStationaryWeight_is_stationary scores hsymm)

/-- The finite softmax Poisson equation is solvable exactly when its source
has zero mean under a supplied normalized stationary row weight. -/
theorem softmaxAttention_poisson_solvable_iff_weightedMean_zero
    (scores : ι → ι → ℝ) (π : ι → ℝ)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * softmaxAttentionMatrix scores i j = π j)
    (b : ι → ℝ) :
    (∃ x : ι → ℝ,
      Matrix.toLin' (1 - softmaxAttentionMatrix scores) x = b) ↔
        weightedMeanMap π b = 0 := by
  have hP : softmaxAttentionMatrix scores ∈ Matrix.rowStochastic ℝ ι :=
    softmaxAttentionMatrix_mem_rowStochastic scores
  have hPpos : ∀ i j, 0 < softmaxAttentionMatrix scores i j := by
    intro i j
    rw [softmaxAttentionMatrix_apply]
    exact softmaxAttentionKernel_pos scores i j
  have hRange := range_laplacian_eq_weightedMean_ker
    (softmaxAttentionMatrix scores) π hP hPpos hπsum hπstat
  constructor
  · rintro ⟨x, hx⟩
    have hbRange : b ∈ LinearMap.range (Matrix.toLin'
        (1 - softmaxAttentionMatrix scores)) := ⟨x, hx⟩
    rw [hRange] at hbRange
    exact LinearMap.mem_ker.mp hbRange
  · intro hmean
    have hbKer : b ∈ LinearMap.ker (weightedMeanMap π) :=
      LinearMap.mem_ker.mpr hmean
    rw [← hRange] at hbKer
    obtain ⟨x, hx⟩ := hbKer
    exact ⟨x, hx⟩

/-- A zero weighted-mean source has the canonical group-inverse solution for
the finite softmax Laplacian, unique among solutions in its range. -/
theorem softmaxAttention_poisson_solution_of_weightedMean_zero
    (scores : ι → ι → ℝ) (π : ι → ℝ)
    (hπsum : ∑ i, π i = 1)
    (hπstat : ∀ j, ∑ i, π i * softmaxAttentionMatrix scores i j = π j)
    (b : ι → ℝ) (hb : weightedMeanMap π b = 0) :
    ∃ D : Module.End ℝ (ι → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - softmaxAttentionMatrix scores)) D ∧
      Matrix.toLin' (1 - softmaxAttentionMatrix scores) (D b) = b ∧
      D b ∈ (Matrix.toLin' (1 - softmaxAttentionMatrix scores)).range ∧
      ∀ x : ι → ℝ,
        x ∈ (Matrix.toLin' (1 - softmaxAttentionMatrix scores)).range →
        Matrix.toLin' (1 - softmaxAttentionMatrix scores) x = b → x = D b := by
  have hP : softmaxAttentionMatrix scores ∈ Matrix.rowStochastic ℝ ι :=
    softmaxAttentionMatrix_mem_rowStochastic scores
  have hPpos : ∀ i j, 0 < softmaxAttentionMatrix scores i j := by
    intro i j
    rw [softmaxAttentionMatrix_apply]
    exact softmaxAttentionKernel_pos scores i j
  exact stochastic_laplacian_poisson_solution_of_weightedMean_zero
    (softmaxAttentionMatrix scores) π hP hPpos hπsum hπstat b hb

/-- For symmetric scores, the softmax Markov Laplacian has a group inverse
whose Green operator is symmetric for the canonical stationary-weighted
pairing. No reciprocity is asserted for asymmetric scores. -/
theorem exists_softmax_groupInverse_green_reciprocity
    (scores : ι → ι → ℝ) (hsymm : ∀ i j, scores i j = scores j i) :
    ∃ G : Matrix ι ι ℝ,
      IsGroupInverse (1 - softmaxAttentionMatrix scores) G ∧
      ∀ x y : ι → ℝ,
        weightedMarkovPairing (softmaxPartitionStationaryWeight scores) x
            (Matrix.mulVec G y) =
          weightedMarkovPairing (softmaxPartitionStationaryWeight scores)
            (Matrix.mulVec G x) y := by
  let P := softmaxAttentionMatrix scores
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P
    (softmaxAttentionMatrix_mem_rowStochastic scores)
  let G : Matrix ι ι ℝ := LinearMap.toMatrix' D
  have hG : IsGroupInverse (1 - P) G := by
    refine ⟨?_, ?_, ?_⟩
    · apply Matrix.toLin'.injective
      simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.1
    · apply Matrix.toLin'.injective
      simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.2.1
    · apply Matrix.toLin'.injective
      simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.2.2
  have hDB : DetailedBalance (softmaxPartitionStationaryWeight scores) P := by
    exact softmaxPartitionStationaryWeight_detailedBalance scores hsymm
  refine ⟨G, hG, ?_⟩
  intro x y
  exact weightedMarkovPairing_groupInverse_symmetric P G
    (softmaxPartitionStationaryWeight scores) x y
    (fun i => (softmaxPartitionStationaryWeight_pos scores i).ne') hDB hG

end InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

end
