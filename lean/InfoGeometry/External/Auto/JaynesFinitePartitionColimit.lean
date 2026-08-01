import Mathlib.Tactic

/-!
# Jaynes Finite Partition Colimit

## Finite Equal Partitions and Dyadic Refinement

Jaynes' finite-sets policy, formalized:

  "Never start with a continuum. Start with finitely many distinguishable
   alternatives. Take the limit only when the transition maps are clear."

This file defines the finite-stage objects used in that policy:

  * finite equal partitions of `[0, 1]`,
  * discrete probability distributions on those partitions,
  * finite Shannon and relative entropy,
  * the dyadic refinement `n ↦ 2n`.

## Finite Refinement Picture

  Partition(n) ──[refine]──→ Partition(2n) ──[refine]──→ ...
       │                            │
       ▼                            ▼
  S_n (finite entropy)        S_{2n} (refined entropy)
       │                            │
       └────────────┬───────────────┘
                    ▼
            compatible finite refinement data

## Finite-Stage Statement

The formal content below stays at finite partitions. It proves the uniform
entropy identity, zero renormalized entropy for the uniform distribution,
self-relative entropy zero, and the cell-width identity for dyadic refinement.

## Connection to Existing Infrastructure

- `JaynesLDDPGNSColimit.lean` — the GNS colimit skeleton already built
- `JaynesFiniteSetsColimitBridge.lean` — the finite-sets policy bridge
- `ContinuumAsColimitCounting.lean` — continuum from finite counting stages
- `PoissonGaussianGNSColimit.lean` — the empirical MCA bridge
- `ChiralCuntzInductive.lean` — Cuntz-Toeplitz inductive refinement
-/

noncomputable section

open Real
open Finset

---------------------------------------------------------------
-- Finite Partitions
---------------------------------------------------------------

/-- A finite partition of the unit interval `[0, 1]` into `n` equal cells.
    Each cell has width 1/n. The partition points are {0, 1/n, 2/n, ..., 1}.

    This is the Jaynesian "finite distinguishable alternatives" —
    the finite starting point used here. -/
structure FinitePartition where
  n : ℕ
  hn : 0 < n
  deriving Repr

/-- The number of cells in the partition. -/
def FinitePartition.cells (P : FinitePartition) : ℕ := P.n

/-- The width of each cell: Δx = 1/n. -/
def FinitePartition.cellWidth (P : FinitePartition) : ℝ := 1 / (P.n : ℝ)

/-- The midpoints of the cells: x_i = (i + 0.5)/n for i = 0,...,n-1. -/
def FinitePartition.midpoints (P : FinitePartition) : List ℝ :=
  List.ofFn fun (i : Fin P.n) => ((i.val : ℝ) + 0.5) / (P.n : ℝ)

/-- A discrete probability distribution on the partition:
    p_i ≥ 0, Σ p_i = 1. -/
structure DiscreteDistribution (P : FinitePartition) where
  prob : Fin P.n → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum_one : (∑ i : Fin P.n, prob i) = 1

/-- The discrete Shannon entropy on a finite partition:
    S(p) = −Σ p_i log p_i. -/
def discreteEntropy {P : FinitePartition} (p : DiscreteDistribution P) : ℝ :=
  -∑ i : Fin P.n, (let pi := p.prob i; if pi > 0 then pi * Real.log pi else 0)

/-- Uniform distribution on the partition: p_i = 1/n for all i. -/
def uniformDistribution (P : FinitePartition) : DiscreteDistribution P where
  prob := fun _ => 1 / (P.n : ℝ)
  prob_nonneg := by
    intro i
    positivity
  prob_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    rw [one_div]
    have h : (P.n : ℝ) ≠ 0 := by exact Nat.cast_ne_zero.mpr (ne_of_gt P.hn)
    exact mul_inv_cancel₀ h

/-- The entropy of the uniform distribution is log(n).
    This is the maximal entropy on a finite set of n alternatives. -/
theorem entropy_uniform_is_log_n (P : FinitePartition) :
    discreteEntropy (uniformDistribution P) = Real.log (P.n : ℝ) := by
  unfold discreteEntropy uniformDistribution
  have hn_pos : 0 < (P.n : ℝ) := Nat.cast_pos.mpr P.hn
  have hn_nz : (P.n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have inv_pos : 0 < (P.n : ℝ)⁻¹ := inv_pos.mpr hn_pos
  simp [inv_pos]
  rw [← mul_assoc]
  rw [mul_inv_cancel₀ hn_nz]
  ring

/-- The renormalized entropy: S(p) − log(n).
    For the uniform distribution, this is 0.
    This subtraction removes the "partition dependence" and
    extracts the intrinsic information content. -/
def renormalizedEntropy {P : FinitePartition} (p : DiscreteDistribution P) : ℝ :=
  discreteEntropy p - Real.log (P.n : ℝ)

/-- Uniform distribution has zero renormalized entropy. -/
theorem renormalized_entropy_uniform_is_zero (P : FinitePartition) :
    renormalizedEntropy (uniformDistribution P) = 0 := by
  rw [renormalizedEntropy, entropy_uniform_is_log_n]
  ring

/-- The relative entropy (Kullback-Leibler divergence) between two
    distributions on the same partition:
    D(p||q) = Σ p_i log(p_i / q_i).

    For identical distributions: D(p||p) = 0 (self-identity). -/
def relativeEntropy {P : FinitePartition} (p q : DiscreteDistribution P) : ℝ :=
  ∑ i : Fin P.n,
    let pi := p.prob i
    let qi := q.prob i
    if pi > 0 ∧ qi > 0 then pi * Real.log (pi / qi) else 0

/-- Relative entropy of a distribution with itself is zero.
    Jaynes' self-consistency condition. -/
theorem relativeEntropy_self_zero {P : FinitePartition} (p : DiscreteDistribution P) :
    relativeEntropy p p = 0 := by
  unfold relativeEntropy
  apply Finset.sum_eq_zero
  intro i hi
  have hpi : p.prob i = p.prob i := rfl
  by_cases hpos : p.prob i > 0
  · simp [hpos]
  · simp [hpos]

---------------------------------------------------------------
-- The Dyadic Refinement Morphism
---------------------------------------------------------------

/-- The dyadic refinement morphism: Partition(n) → Partition(2n).

    Each cell of width 1/n is split into two cells of width 1/(2n).
    The left half corresponds to the first sub-cell, the right half
    to the second.

    Key property: refinement preserves total mass.
    Σ_{i=0}^{2n-1} p'_i = Σ_{i=0}^{n-1} p_i = 1. -/
def dyadicRefinement (P : FinitePartition) : FinitePartition where
  n := 2 * P.n
  hn := by
    have h := P.hn
    omega

/-- The refined cell width is half the original:
    Δx_{2n} = 1/(2n) = (1/n)/2 = Δx_n / 2. -/
theorem refinement_halves_cellWidth (P : FinitePartition) :
    (dyadicRefinement P).cellWidth = P.cellWidth / 2 := by
  unfold FinitePartition.cellWidth dyadicRefinement
  push_cast
  ring

/-- A record carrying the finite partition identities proved in this file. -/
structure JaynesFinitePartitionSynthesis where
  partitionSumOne : ∀ (P : FinitePartition) (p : DiscreteDistribution P),
    (∑ i : Fin P.n, p.prob i) = 1
  uniformEntropyIsLogN : ∀ (P : FinitePartition),
    discreteEntropy (uniformDistribution P) = Real.log (P.n : ℝ)
  relativeEntropySelfZero : ∀ (P : FinitePartition) (p : DiscreteDistribution P),
    relativeEntropy p p = 0

end
