import InfoGeometry.Thermodynamics.FiniteGibbsRelative
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Conditional Fisher / Killing bridge

This file records the Lean-safe comparison theorem between the finite Cartan
Fisher metric and a trace/Killing-type form.

It does **not** define Fisher to be the Killing form.  The only unconditional
theorem is the finite Cartan result already proved in
`CartanExponentialFamily`: at the symmetric point and on centered directions,
the Fisher covariance is the averaged trace form.

A genuine Killing comparison is conditional: a representation must supply a
form whose Cartan restriction agrees with that averaged trace form.  This file
keeps that compatibility as an explicit predicate parameter and derives the
comparison theorem from it.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KillingFisher

open scoped BigOperators
open InfoGeometry.Algebraic.CartanExponentialFamily
open InfoGeometry.Thermodynamics.FiniteGibbsRelative

variable {ι : Type*} [Fintype ι]

/-- Averaged trace form on a finite diagonal Cartan chart. -/
noncomputable def centeredTraceForm (X Y : ι → ℝ) : ℝ :=
  (1 / Fintype.card ι : ℝ) * ∑ i, X i * Y i

/--
Predicate saying that a representation-level trace/Killing readout agrees with
the averaged Cartan trace form on centered directions.

This is deliberately a predicate on an explicit function.  The representation
or Lie-theoretic owner must supply the function and prove this predicate.
-/
def IsCenteredTraceCompatible
    (killingLike : (ι → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∀ X Y : ι → ℝ,
    centered X → centered Y →
      killingLike X Y = centeredTraceForm X Y

/-- The finite Cartan Fisher metric equals the averaged trace form at `θ = 0`. -/
theorem fisher_zero_eq_centeredTraceForm
    [Nonempty ι] (X Y : ι → ℝ) (hX : centered X) (hY : centered Y) :
    fisherMetric (fun _ : ι => (0 : ℝ)) X Y = centeredTraceForm X Y := by
  exact fisherMetric_zero_eq_average_trace_form_of_centered X Y hX hY

/--
Conditional Fisher/Killing comparison.

If a representation-level form restricts to the averaged trace form on centered
Cartan directions, then the symmetric-point Fisher metric equals that form on
those directions.
-/
theorem fisher_zero_eq_killingLike_of_centeredTraceCompatible
    [Nonempty ι]
    (killingLike : (ι → ℝ) → (ι → ℝ) → ℝ)
    (hcompat : IsCenteredTraceCompatible killingLike)
    (X Y : ι → ℝ) (hX : centered X) (hY : centered Y) :
    fisherMetric (fun _ : ι => (0 : ℝ)) X Y = killingLike X Y := by
  rw [fisher_zero_eq_centeredTraceForm X Y hX hY]
  exact (hcompat X Y hX hY).symm

/-- The compatibility predicate can be applied directly to centered directions. -/
theorem centeredTraceCompatible_apply
    (killingLike : (ι → ℝ) → (ι → ℝ) → ℝ)
    (hcompat : IsCenteredTraceCompatible killingLike)
    (X Y : ι → ℝ) (hX : centered X) (hY : centered Y) :
    killingLike X Y = centeredTraceForm X Y :=
  hcompat X Y hX hY

end InfoGeometry.Erlangen.KillingFisher
