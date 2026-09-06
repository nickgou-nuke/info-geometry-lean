import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Geometry.BilingualAnalyticity

noncomputable section

open scoped Topology

namespace InfoGeometry.GrandUnification.AnalyticBridge

open Complex
open InfoGeometry.Geometry.BilingualAnalyticity

/-!
# Annihilation Analytic Bridge

#### BUCKET 1: CLOSED FINITE THEOREMS

* `vacuum_partition_is_analytic_of_mem_nhds`: mathlib's Cauchy-integral
  bridge from complex differentiability on a neighborhood to `AnalyticAt`.
* `vacuum_partition_is_analytic_of_isOpen`: the open-domain specialization.
* `vacuum_partition_is_analytic_on_ball`: the concrete disk-domain
  specialization.
* `vacuum_partition_is_analytic_global`: the whole-plane differentiability
  specialization.
* `vacuum_partition_is_analytic_off_closed_singularSet`: the punctured-domain
  specialization away from an explicit closed singular set.
* `vacuum_partition_cauchyAnalyticAt_of_isOpen`: readback into the repository's
  pointwise phase-linear `CauchyAnalyticAt` structure on the canonical complex
  phase axis.
* `vacuum_partition_cauchyAnalyticAt_on_ball`: disk-domain readback into the
  repository's `CauchyAnalyticAt` structure.
* `vacuum_partition_cauchyAnalyticAt_global`: whole-plane readback into the
  repository's `CauchyAnalyticAt` structure.
* `vacuum_partition_cauchyAnalyticAt_off_closed_singularSet`:
  punctured-domain readback into the repository's `CauchyAnalyticAt` structure.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The closed theorems are conditional on explicit premises:

* `DifferentiableOn ℂ sys.Z_graded D`;
* either `D ∈ 𝓝 s`, or `IsOpen D` and `s ∈ D`.

#### BUCKET 3: OPEN CLOSURE DEBT

None in this file.  No claim is made here that a particular zeta, Weyl,
Cuntz-UHF, or Drazin-Hestenes-Krein object satisfies the differentiability
premise.
-/

/--
Data carrier for a complex partition function on a chosen domain.

Analyticity or differentiability hypotheses are deliberately not stored as
fields; they remain explicit theorem premises.
-/
structure AnalyticPartitionSystem (D : Set ℂ) where
  /-- The graded complex partition function. -/
  Z_graded : ℂ → ℂ

variable {D : Set ℂ} (sys : AnalyticPartitionSystem D)

/--
If the partition function is complex differentiable on a neighborhood of `s`,
then it is analytic at `s` in mathlib's power-series sense.
-/
theorem vacuum_partition_is_analytic_of_mem_nhds
    {s : ℂ}
    (h_diff : DifferentiableOn ℂ sys.Z_graded D)
    (hD : D ∈ 𝓝 s) :
    AnalyticAt ℂ sys.Z_graded s := by
  exact DifferentiableOn.analyticAt h_diff hD

/--
Open-domain specialization of `vacuum_partition_is_analytic_of_mem_nhds`.
-/
theorem vacuum_partition_is_analytic_of_isOpen
    {s : ℂ}
    (h_diff : DifferentiableOn ℂ sys.Z_graded D)
    (h_open : IsOpen D)
    (hs : s ∈ D) :
    AnalyticAt ℂ sys.Z_graded s := by
  exact vacuum_partition_is_analytic_of_mem_nhds sys h_diff (h_open.mem_nhds hs)

/--
The same open-domain result read back into the repository's pointwise
phase-linear Cauchy analytic structure on `ℂ`.
-/
def vacuum_partition_cauchyAnalyticAt_of_isOpen
    {s : ℂ}
    (h_diff : DifferentiableOn ℂ sys.Z_graded D)
    (h_open : IsOpen D)
    (hs : s ∈ D) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure sys.Z_graded s := by
  exact analyticAt_complex_to_cauchyAnalyticAt
    (vacuum_partition_is_analytic_of_isOpen sys h_diff h_open hs)

/--
Concrete local disk version: differentiability on an open metric ball gives
mathlib power-series analyticity at every point of that ball.
-/
theorem vacuum_partition_is_analytic_on_ball
    {c s : ℂ}
    {R : ℝ}
    (sys : AnalyticPartitionSystem (Metric.ball c R))
    (h_diff : DifferentiableOn ℂ sys.Z_graded (Metric.ball c R))
    (hs : s ∈ Metric.ball c R) :
    AnalyticAt ℂ sys.Z_graded s := by
  exact vacuum_partition_is_analytic_of_isOpen
    (D := Metric.ball c R) sys h_diff Metric.isOpen_ball hs

/--
Concrete local disk version, read back into the repository's phase-linear
`CauchyAnalyticAt` structure on `ℂ`.
-/
def vacuum_partition_cauchyAnalyticAt_on_ball
    {c s : ℂ}
    {R : ℝ}
    (sys : AnalyticPartitionSystem (Metric.ball c R))
    (h_diff : DifferentiableOn ℂ sys.Z_graded (Metric.ball c R))
    (hs : s ∈ Metric.ball c R) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure sys.Z_graded s := by
  exact vacuum_partition_cauchyAnalyticAt_of_isOpen
    (D := Metric.ball c R) sys h_diff Metric.isOpen_ball hs

/--
Whole-plane specialization: global complex differentiability gives mathlib
power-series analyticity at every complex point.
-/
theorem vacuum_partition_is_analytic_global
    (sys : AnalyticPartitionSystem Set.univ)
    (h_diff : Differentiable ℂ sys.Z_graded)
    (s : ℂ) :
    AnalyticAt ℂ sys.Z_graded s := by
  exact Differentiable.analyticAt h_diff s

/--
Whole-plane specialization, read back into the repository's phase-linear
`CauchyAnalyticAt` structure on `ℂ`.
-/
def vacuum_partition_cauchyAnalyticAt_global
    (sys : AnalyticPartitionSystem Set.univ)
    (h_diff : Differentiable ℂ sys.Z_graded)
    (s : ℂ) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure sys.Z_graded s := by
  exact analyticAt_complex_to_cauchyAnalyticAt
    (vacuum_partition_is_analytic_global sys h_diff s)

/--
Punctured-domain specialization: if an explicit singular set is closed, then
its complement is open.  Complex differentiability on that complement gives
mathlib power-series analyticity at every nonsingular point.
-/
theorem vacuum_partition_is_analytic_off_closed_singularSet
    {singular : Set ℂ}
    (h_closed : IsClosed singular)
    (sys : AnalyticPartitionSystem singularᶜ)
    (h_diff : DifferentiableOn ℂ sys.Z_graded singularᶜ)
    {s : ℂ}
    (hs : s ∉ singular) :
    AnalyticAt ℂ sys.Z_graded s := by
  exact vacuum_partition_is_analytic_of_isOpen
    (D := singularᶜ) sys h_diff h_closed.isOpen_compl hs

/--
Punctured-domain specialization, read back into the repository's phase-linear
`CauchyAnalyticAt` structure on `ℂ`.
-/
def vacuum_partition_cauchyAnalyticAt_off_closed_singularSet
    {singular : Set ℂ}
    (h_closed : IsClosed singular)
    (sys : AnalyticPartitionSystem singularᶜ)
    (h_diff : DifferentiableOn ℂ sys.Z_graded singularᶜ)
    {s : ℂ}
    (hs : s ∉ singular) :
    CauchyAnalyticAt complexPhaseStructure complexPhaseStructure sys.Z_graded s := by
  exact vacuum_partition_cauchyAnalyticAt_of_isOpen
    (D := singularᶜ) sys h_diff h_closed.isOpen_compl hs

end InfoGeometry.GrandUnification.AnalyticBridge
