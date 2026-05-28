import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.PrimeHurwitzLimit

/-!
# InfoGeometry.Canonical.PrimeMBKSelfAdjointTrace

Witness-gated self-adjointness and extension-trace surface for the
Majorana--Berry--Keating program.

This file does not prove essential self-adjointness of the infinite-volume
Majorana--Berry--Keating operator, does not construct a Krein-space extension,
does not prove trace-class/temperedness of a relative heat kernel, and does not
identify a Mellin transform with the logarithmic derivative of completed `xi`.

It records the finite/infinite MBK operator readouts together with later
analytic socket fields for the unresolved spectral statements.

In this cleanup cycle, the vacuous finite-volume law/certificate wrappers were
removed rather than preserved as proof proxies.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeMBKSelfAdjointTrace

open InfoGeometry.Canonical.PrimeHurwitzLimit

/-! ## Finite and infinite MBK operator data -/

/--
Finite-volume Majorana--Berry--Keating operator data.

The carrier and operator types are parameters because the repo has several
finite/Krein/real-linear shadows.  This packet records the algebraic operator
readouts without choosing a concrete unbounded-operator formalization here.
-/
@[rep_depth operator]
structure FiniteMBKDiracData
    (Cutoff ContinuousHilbert FockSpace Operator PrimeLabel : Type*) where
  cutoff :
    Cutoff
  H_BK :
    Operator
  Q :
    Cutoff → Operator
  D :
    Cutoff → Operator
  D0 :
    Operator
  primeWeight :
    PrimeLabel → ℝ
  rho :
    Operator

/--
Infinite-volume MBK extension packet.

`selfAdjointOrUniqueKreinExtension_law` is intentionally disjunctive at the
interface level: a future analytic owner may prove essential self-adjointness on
a Hilbert domain or unique self-adjoint extension in the chosen Krein metric.
-/
@[rep_depth operator]
structure MBKLimitExtension
    (Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric : Type*) where
  finite :
    FiniteMBKDiracData Cutoff ContinuousHilbert FockSpace Operator PrimeLabel
  limitOperator :
    Operator
  naturalDomain :
    Domain
  kreinMetric :
    KreinMetric
  finite_to_infinite_limit_law : Prop
  finite_to_infinite_limit_certificate :
    finite_to_infinite_limit_law
  selfAdjointOrUniqueKreinExtension_law : Prop
  selfAdjointOrUniqueKreinExtension_certificate :
    selfAdjointOrUniqueKreinExtension_law

namespace MBKLimitExtension

variable {Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric : Type*}
variable
  (E : MBKLimitExtension
    Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric)

/-- Re-export of the infinite-volume limit law. -/
@[rep_depth operator]
theorem finite_to_infinite_limit :
    E.finite_to_infinite_limit_law :=
  E.finite_to_infinite_limit_certificate

/-- Re-export of the supplied self-adjointness/unique-extension law. -/
@[rep_depth operator]
theorem selfAdjointOrUniqueKreinExtension :
    E.selfAdjointOrUniqueKreinExtension_law :=
  E.selfAdjointOrUniqueKreinExtension_certificate

end MBKLimitExtension

/-! ## Relative heat trace and Mellin transform -/

/--
Relative heat-trace packet for the coupled/free MBK pair.

`relativeHeatTrace τ` is the intended readout
`Tr_rel (exp (-τ D²) - exp (-τ D₀²))`.  Well-definedness and temperedness are
analytic laws, stored as certificates.
-/
@[rep_depth operator]
structure RelativeHeatTracePacket
    (Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
      HeatTrace Distribution : Type*) where
  extension :
    MBKLimitExtension
      Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
  relativeHeatTrace :
    ℝ → HeatTrace
  relativeDistribution :
    Distribution
  heatTrace_formula_law : Prop
  heatTrace_formula_certificate :
    heatTrace_formula_law
  wellDefined_for_tau_pos_law : Prop
  wellDefined_for_tau_pos_certificate :
    wellDefined_for_tau_pos_law
  temperedDistribution_law : Prop
  temperedDistribution_certificate :
    temperedDistribution_law

namespace RelativeHeatTracePacket

variable
  {Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
    HeatTrace Distribution : Type*}
variable
  (T : RelativeHeatTracePacket
    Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
    HeatTrace Distribution)

/-- Re-export of the relative heat-trace formula law. -/
@[rep_depth operator]
theorem heatTrace_formula :
    T.heatTrace_formula_law :=
  T.heatTrace_formula_certificate

/-- Re-export of the positive-time well-definedness law. -/
@[rep_depth operator]
theorem wellDefined_for_tau_pos :
    T.wellDefined_for_tau_pos_law :=
  T.wellDefined_for_tau_pos_certificate

/-- Re-export of the tempered-distribution law. -/
@[rep_depth operator]
theorem temperedDistribution :
    T.temperedDistribution_law :=
  T.temperedDistribution_certificate

end RelativeHeatTracePacket

/--
Mellin transform and completed-`xi` logarithmic-derivative packet.

The equality with `- d/ds log ξ(s)` and the singular-support identification are
the hard spectral/analytic trace formula claims.
-/
@[rep_depth operator]
structure MBKMellinXiTracePacket
    (Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
      HeatTrace Distribution MellinReadout SpectralDensity FrequencyReadout : Type*) where
  heatTrace :
    RelativeHeatTracePacket
      Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
      HeatTrace Distribution
  xiZeros :
    CompletedXiZeroPredicate
  mellinTransform :
    ℂ → MellinReadout
  completedXiLogDerivative :
    ℂ → MellinReadout
  spectralDensity :
    SpectralDensity
  zeroFrequency :
    ℂ → FrequencyReadout
  mellin_integral_law : Prop
  mellin_integral_certificate :
    mellin_integral_law
  mellin_eq_neg_dlog_completedXi_law : Prop
  mellin_eq_neg_dlog_completedXi_certificate :
    mellin_eq_neg_dlog_completedXi_law
  singularSupport_eq_xiZeroFrequencies_law : Prop
  singularSupport_eq_xiZeroFrequencies_certificate :
    singularSupport_eq_xiZeroFrequencies_law
  no_unconditional_RH_claim_guard : Type

namespace MBKMellinXiTracePacket

variable
  {Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
    HeatTrace Distribution MellinReadout SpectralDensity FrequencyReadout : Type*}
variable
  (P : MBKMellinXiTracePacket
    Cutoff ContinuousHilbert FockSpace Operator PrimeLabel Domain KreinMetric
    HeatTrace Distribution MellinReadout SpectralDensity FrequencyReadout)

/-- Re-export of the Mellin-integral representation law. -/
@[rep_depth operator]
theorem mellin_integral :
    P.mellin_integral_law :=
  P.mellin_integral_certificate

/-- Re-export of the `- d/ds log ξ(s)` trace identity law. -/
@[rep_depth operator]
theorem mellin_eq_neg_dlog_completedXi :
    P.mellin_eq_neg_dlog_completedXi_law :=
  P.mellin_eq_neg_dlog_completedXi_certificate

/-- Re-export of the singular-support/zero-frequency matching law. -/
@[rep_depth operator]
theorem singularSupport_eq_xiZeroFrequencies :
    P.singularSupport_eq_xiZeroFrequencies_law :=
  P.singularSupport_eq_xiZeroFrequencies_certificate

/--
Owner theorem: the MBK trace packet re-exports the three analytic pillars from
the problem statement.
-/
@[rep_depth operator]
theorem extension_trace_reexports :
    P.heatTrace.extension.selfAdjointOrUniqueKreinExtension_law ∧
      P.heatTrace.temperedDistribution_law ∧
        P.mellin_eq_neg_dlog_completedXi_law ∧
          P.singularSupport_eq_xiZeroFrequencies_law := by
  exact ⟨
    P.heatTrace.extension.selfAdjointOrUniqueKreinExtension,
    P.heatTrace.temperedDistribution,
    P.mellin_eq_neg_dlog_completedXi,
    P.singularSupport_eq_xiZeroFrequencies⟩

end MBKMellinXiTracePacket

end InfoGeometry.Canonical.PrimeMBKSelfAdjointTrace
