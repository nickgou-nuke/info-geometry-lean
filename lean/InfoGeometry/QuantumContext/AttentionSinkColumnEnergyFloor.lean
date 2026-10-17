/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
import InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
import InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics

/-!
# A finite attention-column floor in the pruned GNS energy

For a finite row-softmax attention matrix and a chosen anchor column, strict
positivity yields a uniform positive lower bound on all entries of that
column. The existing pruned-state column estimate then gives a quantitative
lower bound for the full matrix quadratic energy of the attention operator.
The carrier is the full square matrix algebra; it is noncommutative when the
token type has at least two elements.

The theorem concerns finite matrix attention and a chosen positive anchor
weight. It does not assert that the anchor is empirically dominant, derive a
potential or force, or imply gravitational or density-wave dynamics.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionSinkColumnEnergyFloor

open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
open InfoGeometry.QuantumContext.FiniteMarkovDirichletOrderColimit
open InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- On a finite token carrier, strict softmax positivity gives a single
positive floor for every entry in the selected attention column. -/
theorem exists_attention_anchor_column_floor
    (scores : ι → ι → ℝ) (β : ℝ) (anchor : ι) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ attentionCouplingMatrix scores β i anchor := by
  exact exists_target_minorization_of_positive
    (attentionCouplingMatrix scores β) anchor
    (fun i j => attentionCouplingMatrix_pos scores β i j)

/-- A uniform positive attention floor in the anchor column forces a
quantitative lower bound on the pruned GNS quadratic energy of the full
attention matrix. The bound scales with the number of rows and the state
weight of the anchor. -/
theorem pruned_attention_energy_ge_anchor_floor
    (pw : PrunedWeights ι) (anchor : ι)
    (scores : ι → ι → ℝ) (β ε : ℝ)
    (hε : 0 < ε)
    (hfloor : ∀ i, ε ≤ attentionCouplingMatrix scores β i anchor) :
    pw.weights anchor * (Fintype.card ι : ℝ) * ε ^ 2 ≤
      prunedState pw
        ((attentionCouplingMatrix scores β).transpose * attentionCouplingMatrix scores β) := by
  have hsq : ∀ i, ε ^ 2 ≤ (attentionCouplingMatrix scores β i anchor) ^ 2 := by
    intro i
    have hpos := attentionCouplingMatrix_pos scores β i anchor
    nlinarith [hfloor i, hε]
  have hsum : (Fintype.card ι : ℝ) * ε ^ 2 ≤
      ∑ i, (attentionCouplingMatrix scores β i anchor) ^ 2 := by
    have hsum' : ∑ i : ι, ε ^ 2 ≤
        ∑ i : ι, (attentionCouplingMatrix scores β i anchor) ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    simpa using hsum'
  have hweighted := mul_le_mul_of_nonneg_left hsum (pw.nonneg anchor)
  calc
    pw.weights anchor * (Fintype.card ι : ℝ) * ε ^ 2 =
        pw.weights anchor * ((Fintype.card ι : ℝ) * ε ^ 2) := by ring
    _ ≤ pw.weights anchor *
        (∑ i, (attentionCouplingMatrix scores β i anchor) ^ 2) := hweighted
    _ ≤ prunedState pw
        ((attentionCouplingMatrix scores β).transpose * attentionCouplingMatrix scores β) :=
      prunedState_ge_anchor_column_normSq pw anchor (attentionCouplingMatrix scores β)

/-- Combining finite softmax minorization with the full-matrix GNS estimate
produces an explicit positive column floor and its quantitative energy bound
for any pruned state. The bound is strictly positive whenever the anchor has
positive pruned-state weight. -/
theorem exists_pruned_attention_energy_floor
    (pw : PrunedWeights ι) (anchor : ι)
    (scores : ι → ι → ℝ) (β : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i, ε ≤ attentionCouplingMatrix scores β i anchor) ∧
      pw.weights anchor * (Fintype.card ι : ℝ) * ε ^ 2 ≤
        prunedState pw
          ((attentionCouplingMatrix scores β).transpose * attentionCouplingMatrix scores β) := by
  obtain ⟨ε, hε, hfloor⟩ := exists_attention_anchor_column_floor scores β anchor
  exact ⟨ε, hε, hfloor,
    pruned_attention_energy_ge_anchor_floor pw anchor scores β ε hε hfloor⟩

end InfoGeometry.QuantumContext.AttentionSinkColumnEnergyFloor
