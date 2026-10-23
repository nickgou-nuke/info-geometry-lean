/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.AttentionFrameCorrections
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A normalized measurement from the existing overcomplete attention keys

Contract: retain `AttentionFrameCorrections.key` and its full real matrix state
carrier. Apply the symmetric inverse square root of the key frame operator
to all three keys. Their positive rank-one effects sum to the identity, so
every positive trace-one matrix gives a probability row. No softmax equality
is asserted. This resolves the normalization failure of the original raw
readouts without discarding an outcome or imposing orthogonality on the keys.

The frame operator is `I + v vᵀ`, where `v = key 2` is unit. Whitening is
`I + (sqrt 2 / 2 - 1) v vᵀ`. Exact coordinate evidence is reproducible with
`scripts/check_attention_frame_whitening.py`; the theorems below are native
Lean proofs. The consumer is `Canonical.ProjectiveZornAttention`.
-/

noncomputable section
namespace InfoGeometry.LLM.AttentionFrameWhitening

open AttentionFrameCorrections Matrix
open scoped BigOperators Matrix

/-- Symmetric whitening of the original three-key frame. -/
def whitening : Mat2 :=
  1 + (Real.sqrt 2 / 2 - 1) • vecMulVec (key 2) (key 2)

def whitenedKey (k : Fin 3) : Fin 2 → ℝ := whitening *ᵥ key k

def effect (k : Fin 3) : Mat2 := vecMulVec (whitenedKey k) (whitenedKey k)

theorem whitening_frame_whitening :
    whitening * (∑ k : Fin 3, vecMulVec (key k) (key k)) * whitening = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [whitening, key, Fin.sum_univ_succ, Matrix.mul_apply,
      Matrix.vecMulVec, Matrix.smul_apply, Matrix.one_apply] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

theorem effect_posSemidef (k : Fin 3) : (effect k).PosSemidef := by
  simpa [effect] using Matrix.posSemidef_vecMulVec_self_star (whitenedKey k)

theorem sum_effect : ∑ k : Fin 3, effect k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [effect, whitenedKey, whitening, key, Fin.sum_univ_succ,
      Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.smul_apply, Matrix.one_apply] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

/-- Born readout of the whitened key, linear in the full matrix state. -/
def readout (ρ : Mat2) (k : Fin 3) : ℝ :=
  whitenedKey k ⬝ᵥ (ρ *ᵥ whitenedKey k)

theorem readout_nonneg {ρ : Mat2} (hρ : ρ.PosSemidef) (k : Fin 3) :
    0 ≤ readout ρ k := by
  simpa [readout] using hρ.dotProduct_mulVec_nonneg (whitenedKey k)

theorem readout_eq_trace (ρ : Mat2) (k : Fin 3) :
    readout ρ k = Matrix.trace (ρ * effect k) := by
  simp [readout, effect, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec, Fin.sum_univ_two]
  ring

theorem sum_readout (ρ : Mat2) : ∑ k : Fin 3, readout ρ k = Matrix.trace ρ := by
  simp_rw [readout_eq_trace]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_effect, mul_one]

theorem readout_probability {ρ : Mat2} (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) :
    (∀ k, 0 ≤ readout ρ k) ∧ (∑ k : Fin 3, readout ρ k) = 1 :=
  ⟨readout_nonneg hρ, (sum_readout ρ).trans htrace⟩

theorem maximallyMixed_readouts :
    (fun k => readout ((1 / 2 : ℝ) • (1 : Mat2)) k) =
      ![41 / 100, 17 / 50, 1 / 4] := by
  funext k
  fin_cases k <;>
    norm_num [readout, whitenedKey, whitening, key, Fin.sum_univ_succ,
      Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.smul_apply] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

end InfoGeometry.LLM.AttentionFrameWhitening
