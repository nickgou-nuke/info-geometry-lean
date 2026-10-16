/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PMFKernelCompositionScratch

variable {α β : Type*} [MeasurableSpace α] [Countable α]
  [MeasurableSingletonClass α] [MeasurableSpace β]

/-- PMF bind agrees, after `toMeasure`, with composing the input measure
with the countable kernel of continuation measures. -/
theorem toMeasure_bind_eq_comp (p : PMF α) (q : α → PMF β) :
    (p.bind q).toMeasure =
      Kernel.ofFunOfCountable (fun a => (q a).toMeasure) ∘ₘ p.toMeasure := by
  ext s hs
  rw [PMF.toMeasure_bind_apply (p := p) (f := q) s hs]
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  rw [lintegral_countable']
  apply tsum_congr
  intro a
  rw [Kernel.ofFunOfCountable,
    PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)]
  exact mul_comm _ _

end PMFKernelCompositionScratch
