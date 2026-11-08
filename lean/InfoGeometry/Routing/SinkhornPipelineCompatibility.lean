/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.SinkhornBranchCompatibility

/-!
# Normalized readout compatibility

Exponentiating token logits converts native product inputs to calibrated
inputs. The resulting normalized outputs agree; raw outputs are not equated.
-/
namespace InfoGeometry.Routing.BlockCausalSinkhorn
open scoped BigOperators
open InfoGeometry.Routing.CausalPrefixPooling
noncomputable section
variable {C L K D : Type*} [Fintype K]

/-- Convert log detector weights to positive raw weights, preserving features. -/
def toCalibratedInput (x : ChunkData L K D) : ChunkInput L K D where
  m_shape := x.1
  K_chunk := x.2.1 0
  V_shape := x.2.1 1
  Q_lat := x.2.1 2
  V_det := x.2.1 3
  V_tok := fun j k => Real.exp (x.2.2 j k)

theorem responsibility_eq_gain_ratio [Nonempty K]
    (S : Matrix K K ℝ) (T : ℕ) (v : Matrix L K ℝ) (j : L) (k : K) :
    responsibility S T v j k =
      (Real.exp (v j k) * FiniteLogSinkhorn.sinkhornDetGain T S k) /
        ∑ l, Real.exp (v j l) * FiniteLogSinkhorn.sinkhornDetGain T S l := by
  have hp : 0 < ∑ l, Real.exp (v j l + logDetectorGain S T l) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold responsibility logSumExp
  rw [Real.exp_sub, Real.exp_log hp]
  simp_rw [Real.exp_add, exp_logDetectorGain_eq]

section Prefix
variable [Fintype C] [LinearOrder C]

omit [Fintype K] in
theorem prefix_weight_eq (m : C → K → ℝ) (t s : C) (k : K) :
    weight (prefixSet t) (fun r => m r k) s = causalPrefixWeights m t s k := by
  simp [weight, prefixSet, partition, causalPrefixWeights, causalPrefixPart]

omit [Fintype K] in
theorem pooledFeature_eq_calibrated (x : C → ChunkData L K D) (t : C) (a : Fin 4) :
    pooledFeature x t a =
      causalPrefixPool (causalPrefixWeights (fun s => (x s).1))
        (fun s => (x s).2.1 a) t := by
  ext k d
  simp only [pooledFeature, pool, causalPrefixPool, prefix_weight_eq]

omit [Fintype K] in
theorem logScore_eq_calibrated (x : C → ChunkData L K D) (t : C)
    [Fintype D] (tau : ℝ) (prior : Matrix K K ℝ) :
    logScore x t tau prior =
      blockCausalLogScore (fun s => toCalibratedInput (x s)) tau prior t := by
  unfold logScore blockCausalLogScore
  rw [pooledFeature_eq_calibrated]
  rfl

/-- The logarithmic responsibility pipeline equals the normalized calibrated
pipeline under the explicit conversion, for any supplied channel processor. -/
theorem output_eq_normalized_calibrated [Nonempty K] [Fintype L] [Fintype D]
    (psi : Matrix K K ℝ → Matrix K D ℝ → Matrix K D ℝ → Matrix K D ℝ)
    (T : ℕ) (tau : ℝ) (prior : Matrix K K ℝ)
    (x : C → ChunkData L K D) (t : C) :
    output psi T tau prior x t =
      normalizedChunkOutput psi T tau prior (fun s => toCalibratedInput (x s)) t := by
  classical
  ext j a
  rw [normalizedChunkOutput_eq_responsibility_readout]
  simp only [output, Matrix.mul_apply, responsibility_eq_gain_ratio,
    core_eq_sinkhornMatrix, logScore_eq_calibrated, pooledFeature_eq_calibrated,
    detectorMass, toCalibratedInput]

end Prefix
end
end InfoGeometry.Routing.BlockCausalSinkhorn
