/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
import InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge

/-!
# Rowwise bridge between softmax states and Markov kernels

The finite Markov owner uses a row-normalized score matrix, while the attention
state owner uses a normalized logit vector. Scaling each score row by `β`
identifies these existing definitions exactly. The theorem is rowwise: it does
not identify the full transition matrix with a single density matrix.
-/

namespace InfoGeometry.QuantumContext.SoftmaxKMSMarkovBridge

open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

variable {ι : Type*} [Fintype ι]

/-- A row of the scaled score softmax is the existing vector softmax state. -/
theorem softmaxAttentionKernel_eq_softmaxWeight_row
    (scores : ι → ι → ℝ) (β : ℝ) (i j : ι) :
    softmaxAttentionKernel (fun r c => β * scores r c) i j =
      softmaxWeight (scores i) β j := by
  simp [softmaxAttentionKernel, gibbsCouplingWeight, queryPartitionFunction,
    softmaxWeight]

/-- The diagonal density entry for one query row equals the corresponding
entry of the finite row-stochastic attention kernel. -/
theorem attentionDensityMatrix_diagonal_eq_softmaxAttentionKernel
    [DecidableEq ι] (scores : ι → ι → ℝ) (β : ℝ) (i j : ι) :
    attentionDensityMatrix (scores i) β j j =
      softmaxAttentionKernel (fun r c => β * scores r c) i j := by
  rw [softmaxAttentionKernel_eq_softmaxWeight_row]
  simp [attentionDensityMatrix, Matrix.diagonal_apply]

/-- The existing attention state evaluates an observable by averaging its
diagonal entries against the corresponding row of the finite transition
kernel. This transports rowwise softmax weights into the existing state and
GNS/KMS interface. -/
theorem attentionState_eq_row_kernel_diagonal_expectation
    [DecidableEq ι] (scores : ι → ι → ℝ) (β : ℝ) (i : ι)
    (A : Matrix ι ι ℝ) :
    attentionState (scores i) β A =
      ∑ j, softmaxAttentionKernel (fun r c => β * scores r c) i j * A j j := by
  rw [attentionState_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [softmaxAttentionKernel_eq_softmaxWeight_row]

/-! ### Specialization to the polarized attention owner

For the repository's positive-sheet split attention, each fixed query row is
the diagonal weight distribution of its corresponding finite attention state.
The statement remains rowwise: it does not identify the full transition matrix
with one density matrix.
-/

section PolarizedAttention

open InfoGeometry.Canonical.Attention

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedBridgeFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- The softmax weight of the positive-sheet score equals the corresponding
entry of the repository's polarized attention weight vector. -/
theorem polarizedPlusAttentionWeight_eq_softmaxWeight
    (q : E) (ctx : ContextWindow n E V) (β : ℝ) (j : Fin n) :
    softmaxWeight (fun k => polarizedPlusScore (E := E) q (ctx.keys k)) β j =
      polarizedPlusAttentionWeights (E := E) (V := V) q ctx β j := by
  rw [← gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights
    (E := E) (V := V) q ctx β j]
  simp only [softmaxWeight, InfoGeometry.GrandCanonical.gibbsWeight,
    InfoGeometry.GrandCanonical.partition, polarizedPlusParams]
  congr 1
  · congr 1 <;> ring
  · apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ring

/-- The concrete polarized attention matrix row reproduces the diagonal
expectation of its associated KMS state for every matrix observable. -/
theorem polarizedAttentionState_eq_row_diagonal_expectation
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (i : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    attentionState
        (fun j => polarizedPlusScore (E := E) (queries i) (ctx.keys j)) β A =
      ∑ j, polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j * A j j := by
  rw [attentionState_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [polarizedPlusAttentionMatrix_apply,
    polarizedPlusAttentionWeight_eq_softmaxWeight (E := E) (V := V)
      (queries i) ctx β j]

/-- The polarized attention state for one query satisfies the finite matrix
KMS trace identity with its own diagonal density matrix and inverse. -/
theorem polarizedAttentionState_kms
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (i : Fin n) (A B : Matrix (Fin n) (Fin n) ℝ) :
    let logits := fun j => polarizedPlusScore (E := E) (queries i) (ctx.keys j)
    attentionState logits β
        (A * (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β)) =
      attentionState logits β (B * A) := by
  exact attentionState_kms
    (fun j => polarizedPlusScore (E := E) (queries i) (ctx.keys j)) β A B

end PolarizedAttention

end InfoGeometry.QuantumContext.SoftmaxKMSMarkovBridge
