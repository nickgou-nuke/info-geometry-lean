/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionLogPartitionModularBridge
import InfoGeometry.QuantumContext.LinShuKMSPetzRadialSynthesis

/-!
# Softmax Sink Coefficient at the Log-Partition Radius

This module composes the finite softmax/log-partition definitions with the existing
Lin–Shu radial model. For logits `logits`, the energy `-logits` makes the partition
sum exactly the softmax denominator. Evaluating the chosen logarithmic monopole at
that positive radius gives its log-partition expression and specializes the existing
derivative, circular-balance, and epicyclic identities.

The radial logarithmic potential remains a separately chosen model in
`LinShuKMSPetzRadialSynthesis`: these results do not derive it from the vector-valued
attention sink potential in `LinShuAttentionDensityWave`.

The positive partition sum used here is an input radius for that radial model. It is not the
Poincaré-disk coordinate `tanh (β / 2)`; no thermodynamic-to-hyperbolic-distance map is asserted.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.KMSSinkPartitionRadiusBridge

open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionLogPartitionModularBridge
open InfoGeometry.QuantumContext.LinShuKMSPetzRadialSynthesis
open InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics

/-! ### The finite softmax radius and its sink coefficient -/

private theorem softmaxSinkCoefficient_nonneg {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ : ℝ) :
    0 ≤ sinkCircularVelSq (softmaxWeight logits β) σ₀ := by
  unfold sinkCircularVelSq
  exact mul_nonneg (le_of_lt (softmaxWeight_pos logits β 0)) (sq_nonneg σ₀)

/-- The partition sum for energy `-logits` is exactly the denominator used by
the existing softmax weights. -/
theorem softmaxWeight_eq_exp_div_partitionZ {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β : ℝ) (i : Fin (n + 1)) :
    softmaxWeight logits β i =
      Real.exp (β * logits i) / partitionZ (fun j => -logits j) β := by
  have hden : (∑ j, Real.exp (β * logits j)) =
      partitionZ (fun j => -logits j) β := by
    unfold partitionZ
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring
  unfold softmaxWeight
  rw [hden]

/-- At the partition radius formed from energy `-logits`, the existing radial
logarithmic monopole is the sink coefficient times the existing log-partition
potential. This is a specialization of the radial model, not a derivation of
that model from the vector-valued attention sink. -/
theorem softmaxSink_logMonopole_eq_logPartition {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ : ℝ) :
    logMonopolePotential
        (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀))
        (partitionZ (fun j => -logits j) β) =
      sinkCircularVelSq (softmaxWeight logits β) σ₀ *
        logPartitionPotential (fun j => -logits j) β := by
  have hcoef := softmaxSinkCoefficient_nonneg logits β σ₀
  simp only [logMonopolePotential,
    InfoGeometry.Canonical.RadialQuantizationFiveGradedCylinder.radialTime,
    InfoGeometry.Convex.RadialLogBarrier.radialTau, logPartitionPotential]
  rw [Real.sq_sqrt hcoef]

/-- The same specialization, now stated directly for the `i`th row of the
repository's finite attention coupling matrix. The radial potential is still
the separately chosen model documented above. -/
theorem attentionRowSink_logMonopole_eq_logPartition {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β σ₀ : ℝ)
    (i : Fin (n + 1)) :
    logMonopolePotential
        (Real.sqrt (sinkCircularVelSq (attentionCouplingMatrix scores β i) σ₀))
        (partitionZ (fun j => -scores i j) β) =
      sinkCircularVelSq (attentionCouplingMatrix scores β i) σ₀ *
        logPartitionPotential (fun j => -scores i j) β := by
  exact softmaxSink_logMonopole_eq_logPartition (scores i) β σ₀

/-- The radial derivative of the softmax-parameterized logarithmic monopole,
evaluated at the actual finite partition radius `Z`. -/
theorem hasDerivAt_softmaxSink_logMonopole_at_partitionRadius {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ : ℝ) :
    HasDerivAt
      (logMonopolePotential
        (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀)))
      (sinkCircularVelSq (softmaxWeight logits β) σ₀ /
        partitionZ (fun j => -logits j) β)
      (partitionZ (fun j => -logits j) β) := by
  have hcoef := softmaxSinkCoefficient_nonneg logits β σ₀
  have hr := ne_of_gt (partitionZ_pos (fun j => -logits j) β)
  convert hasDerivAt_logMonopolePotential
      (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀)) hr using 1
  rw [Real.sq_sqrt hcoef]

/-- The softmax sink specialization satisfies the existing `α = 1`
centrifugal-balance identity at the partition radius. -/
theorem softmaxSink_centrifugalBalance_at_partitionRadius {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ : ℝ) :
    deriv
        (logMonopolePotential
          (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀)))
        (partitionZ (fun j => -logits j) β) =
      partitionZ (fun j => -logits j) β *
        (powerLawOmega
          (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀)) 1
          (partitionZ (fun j => -logits j) β)) ^ 2 := by
  exact kmsSinkLogPotential_generates_alpha_one_flatRotationCurve
    (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀))
    (partitionZ (fun j => -logits j) β)
    (ne_of_gt (partitionZ_pos (fun j => -logits j) β))

/-- The epicyclic frequency at the softmax partition radius is determined by
the selected sink coefficient and `Z`: `κ² = 2 (ρ₀ σ₀²) / Z²`. -/
theorem softmaxSink_epicyclicFreqSq_at_partitionRadius {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ : ℝ) :
    powerLawEpicyclicFreqSq
        (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀)) 1
        (partitionZ (fun j => -logits j) β) =
      2 * sinkCircularVelSq (softmaxWeight logits β) σ₀ /
        (partitionZ (fun j => -logits j) β) ^ 2 := by
  have hcoef := softmaxSinkCoefficient_nonneg logits β σ₀
  have hZ := partitionZ_pos (fun j => -logits j) β
  rw [kmsSink_flatRotationCurve_epicyclicFreqSq
      (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀))
      (partitionZ (fun j => -logits j) β) (ne_of_gt hZ),
    deriv_logMonopolePotential
      (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀))
      (partitionZ (fun j => -logits j) β) (ne_of_gt hZ),
    Real.sq_sqrt hcoef]
  field_simp [ne_of_gt hZ]

/-- Strict epicyclic positivity at the finite softmax partition radius for a
positive sink value scale. -/
theorem softmaxSink_epicyclicFreqSq_pos_at_partitionRadius {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    0 < powerLawEpicyclicFreqSq
      (Real.sqrt (sinkCircularVelSq (softmaxWeight logits β) σ₀)) 1
      (partitionZ (fun j => -logits j) β) := by
  exact kmsSoftmaxSink_pos_implies_rayleigh_epicyclic_pos logits β σ₀
    (partitionZ (fun j => -logits j) β) hσ₀
    (partitionZ_pos (fun j => -logits j) β)

end InfoGeometry.QuantumContext.KMSSinkPartitionRadiusBridge
