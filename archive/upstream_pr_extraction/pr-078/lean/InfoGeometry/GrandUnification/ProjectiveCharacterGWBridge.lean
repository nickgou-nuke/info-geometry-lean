import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite readout transport lemmas

This module contains only native transport facts for finite readouts.  It does
not package a supplied equality as a theorem with the same proposition, and it
does not assert a Gromov--Witten invariant, a projective character theorem, or
an analytic partition-function identity.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.GrandUnification

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
