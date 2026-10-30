/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.QuantumContext.AttentionGNSBridge
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
# Additive score gauge invariance at the attention KMS/GNS boundary

Adding one common constant to all finite logits leaves the normalized attention
state and the existing finite real-time modular flow unchanged. This records
the projective score gauge directly on the KMS/GNS owners. It does not identify
Fourier positional heads or Mellin/Laplace transforms with that state.
-/

namespace InfoGeometry.QuantumContext.AttentionGaugeGNSBridge

open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A common additive logit shift cancels from the normalized softmax law. -/
theorem softmaxWeight_add_const (logits : ι → ℝ) (β c : ℝ) (i : ι) :
    softmaxWeight (fun j => logits j + c) β i = softmaxWeight logits β i := by
  have hexp : Real.exp (β * c) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hnum : Real.exp (β * (logits i + c)) =
      Real.exp (β * logits i) * Real.exp (β * c) := by
    rw [mul_add, Real.exp_add]
  have hden : (∑ j, Real.exp (β * (logits j + c))) =
      (∑ j, Real.exp (β * logits j)) * Real.exp (β * c) := by
    simp_rw [mul_add, Real.exp_add]
    rw [Finset.sum_mul]
  dsimp [softmaxWeight]
  rw [hnum, hden]
  field_simp

/-- The diagonal density operator representing the attention state is gauge invariant. -/
theorem attentionDensityMatrix_add_const [DecidableEq ι]
    (logits : ι → ℝ) (β c : ℝ) :
    attentionDensityMatrix (fun i => logits i + c) β =
      attentionDensityMatrix logits β := by
  ext i j
  simp [attentionDensityMatrix, softmaxWeight_add_const]

/-- The GNS pre-inner product induced by the attention density is unchanged by
a common additive logit shift. Hence the state-null relation used by the
existing algebraic GNS quotient is unchanged as well. -/
theorem attentionGNSInner_add_const [DecidableEq ι]
    (logits : ι → ℝ) (β c : ℝ) (A B : Matrix ι ι ℝ) :
    InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (attentionDensityMatrix (fun i => logits i + c) β) A B =
      InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (attentionDensityMatrix logits β) A B := by
  rw [attentionDensityMatrix_add_const]

/-- The finite attention state functional is invariant under a common logit shift. -/
theorem attentionState_add_const [DecidableEq ι] (logits : ι → ℝ) (β c : ℝ)
    (A : Matrix ι ι ℝ) :
    attentionState (fun i => logits i + c) β A = attentionState logits β A := by
  rw [attentionState_eq_sum, attentionState_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [softmaxWeight_add_const]

/-- The actual finite modular automorphism depends only on score differences,
so it is unchanged by the same projective logit gauge. -/
theorem modularFlow_add_const [DecidableEq ι]
    (logits : ι → ℝ) (β c t : ℝ) (A : Matrix ι ι ℂ) :
    modularFlow (fun i => logits i + c) β t A = modularFlow logits β t A := by
  ext i j
  rw [modularFlow_apply_eq_exp_sub, modularFlow_apply_eq_exp_sub]
  congr 1
  congr 1
  congr 1
  ring_nf

end InfoGeometry.QuantumContext.AttentionGaugeGNSBridge
