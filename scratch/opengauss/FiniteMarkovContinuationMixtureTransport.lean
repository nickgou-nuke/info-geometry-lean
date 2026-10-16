/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.PMFKernelComposition
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Continuation mixture transport

This leaf transports a state-indexed continuation PMF through a measure on
histories when that measure's endpoint marginal is a PMF. It is the measure
factorization needed by a first-transition induction for finite Markov paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InfoGeometry.QuantumContext.FiniteMarkovContinuationMixtureTransport

variable {H ι β : Type*} [MeasurableSpace H] [Countable H]
  [MeasurableSingletonClass H] [MeasurableSpace ι] [Countable ι]
  [MeasurableSingletonClass ι] [MeasurableSpace β]

/-- A deterministic history endpoint followed by state-dependent PMF
continuations has the same output law as the corresponding PMF bind. -/
theorem endpoint_marginal_continuation_bind
    (μ : Measure H) (endpoint : H → ι) (hendpoint : Measurable endpoint)
    (p : PMF ι) (hp : Measure.map endpoint μ = p.toMeasure)
    (q : ι → PMF β) :
    Kernel.ofFunOfCountable (fun h => (q (endpoint h)).toMeasure) ∘ₘ μ =
      (p.bind q).toMeasure := by
  let endpointKernel : Kernel H ι := Kernel.deterministic endpoint hendpoint
  let continuationKernel : Kernel ι β :=
    Kernel.ofFunOfCountable (fun i => (q i).toMeasure)
  have hcomp :
      (continuationKernel ∘ₖ endpointKernel) ∘ₘ μ =
        continuationKernel ∘ₘ (endpointKernel ∘ₘ μ) := by
    exact Measure.comp_assoc.symm
  have hendpointKernel : endpointKernel ∘ₘ μ = Measure.map endpoint μ := by
    exact Measure.deterministic_comp_eq_map hendpoint
  have hkernel :
      continuationKernel ∘ₖ endpointKernel =
        Kernel.ofFunOfCountable (fun h => (q (endpoint h)).toMeasure) := by
    ext h
    rw [Kernel.comp_apply, Kernel.deterministic_apply hendpoint h]
    rw [Measure.dirac_bind continuationKernel.measurable]
    rfl
  rw [← hkernel, hcomp, hendpointKernel, hp]
  exact (InfoGeometry.Probability.PMFKernelComposition.toMeasure_bind_eq_comp p q).symm

end InfoGeometry.QuantumContext.FiniteMarkovContinuationMixtureTransport
