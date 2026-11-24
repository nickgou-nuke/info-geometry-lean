/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Fintype.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Projective character / Gromov--Witten bridge, canonical surface

This file avoids local bridge packets and target wrappers.  It records only
finite/readout identities stated directly with functions, finite sums, `Real.log`,
and `Real.exp`.

No Gromov--Witten invariant, virtual localization formula, quantum metric
convergence theorem, or geometric correspondence theorem is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.GrandUnification

/-- A directly supplied partition/trace equality is the partition/trace readout. -/
theorem projectiveCharacter_partitionReadout_is_traceReadout
    (Parameter Operator : Type*)
    (partitionFunction : Parameter → ℝ)
    (traceReadout : Operator → ℝ)
    (untracedExponential : Parameter → Operator)
    (h_partition : ∀ β, partitionFunction β = traceReadout (untracedExponential β))
    (β : Parameter) :
    partitionFunction β = traceReadout (untracedExponential β) := by
  exact h_partition β

/-- Log-partition is the logarithm of the supplied trace/readout. -/
theorem projectiveCharacter_logPartition_is_log_trace
    (Parameter Operator : Type*)
    (partitionPotential partitionFunction : Parameter → ℝ)
    (traceReadout : Operator → ℝ)
    (untracedExponential : Parameter → Operator)
    (h_log : ∀ β, partitionPotential β = Real.log (partitionFunction β))
    (h_partition : ∀ β, partitionFunction β = traceReadout (untracedExponential β))
    (β : Parameter) :
    partitionPotential β = Real.log (traceReadout (untracedExponential β)) := by
  rw [h_log β, h_partition β]

/-- KL readout equality from explicitly supplied expectation/log-density data. -/
theorem projectiveCharacter_kl_eq_expectation_logDensity
    (State : Type*)
    (KL : ℝ)
    (expectationNu : (State → ℝ) → ℝ)
    (logDensity : State → ℝ)
    (hKL : KL = expectationNu logDensity) :
    KL = expectationNu logDensity := by
  exact hKL

/-- Finite spectral partition normalization in direct finite-sum form. -/
theorem projectiveCharacter_finiteSpectral_partitionNormalization
    (S : Type*) [Fintype S]
    (partition inverseTemperature : ℝ)
    (spectralEnergy spectralVolume : S → ℝ)
    (h_partition :
      partition =
        ∑ s : S,
          Real.exp (-(inverseTemperature * spectralEnergy s)) * spectralVolume s) :
    partition =
      ∑ s : S,
        Real.exp (-(inverseTemperature * spectralEnergy s)) * spectralVolume s := by
  exact h_partition

/-- Projective diagonal shadow readout, stated as the same direct finite-sum equality. -/
theorem finite_projective_shadow_only_ofModularReadout
    (S : Type*) [Fintype S]
    (partition inverseTemperature : ℝ)
    (spectralEnergy spectralVolume : S → ℝ)
    (h_partition :
      partition =
        ∑ s : S,
          Real.exp (-(inverseTemperature * spectralEnergy s)) * spectralVolume s) :
    partition =
      ∑ s : S,
        Real.exp (-(inverseTemperature * spectralEnergy s)) * spectralVolume s := by
  exact projectiveCharacter_finiteSpectral_partitionNormalization
    S partition inverseTemperature spectralEnergy spectralVolume h_partition

/-- Applying `Real.log` transports an equality of positive readouts. -/
theorem log_readout_congr
    {x y : ℝ} (hxy : x = y) : Real.log x = Real.log y := by
  exact congrArg Real.log hxy

/-- Compose a logarithmic potential readout with a partition/trace readout. -/
theorem log_partitionReadout_of_equalities
    {Parameter Operator : Type*}
    (partitionPotential partitionFunction : Parameter → ℝ)
    (traceReadout : Operator → ℝ)
    (untracedExponential : Parameter → Operator)
    (h_log : ∀ β, partitionPotential β = Real.log (partitionFunction β))
    (h_partition : ∀ β, partitionFunction β = traceReadout (untracedExponential β))
    (β : Parameter) :
    partitionPotential β = Real.log (traceReadout (untracedExponential β)) := by
  rw [h_log β, h_partition β]

/-- Transport an equality through an arbitrary expectation functional. -/
theorem expectation_readout_congr
    {State : Type*}
    (expectation : (State → ℝ) → ℝ)
    {f g : State → ℝ}
    (hfg : f = g) : expectation f = expectation g := by
  rw [hfg]

/-- Finite sums respect pointwise equality of their summands. -/
theorem finite_sum_readout_congr
    {S : Type*} [Fintype S]
    (f g : S → ℝ)
    (hfg : ∀ s, f s = g s) :
    (∑ s : S, f s) = ∑ s : S, g s := by
  apply Finset.sum_congr rfl
  intro s hs
  exact hfg s

/-- A finite partition readout is transported by a termwise equality. -/
theorem finite_partition_readout_congr
    {S : Type*} [Fintype S]
    (partition : ℝ)
    (f g : S → ℝ)
    (h_partition : partition = ∑ s : S, f s)
    (hfg : ∀ s, f s = g s) :
    partition = ∑ s : S, g s := by
  rw [h_partition, finite_sum_readout_congr f g hfg]

end InfoGeometry.GrandUnification
