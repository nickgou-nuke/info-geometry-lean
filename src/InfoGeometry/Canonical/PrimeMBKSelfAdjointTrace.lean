import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

This is data only.  Essential self-adjointness or uniqueness of a Krein-space
extension is not asserted here.
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

/-! ## Relative heat trace and Mellin transform -/

/--
Relative heat-trace packet for the coupled/free MBK pair.

`relativeHeatTrace τ` is the intended readout
`Tr_rel (exp (-τ D²) - exp (-τ D₀²))`.  Well-definedness and temperedness are
not asserted in this data packet.
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

end InfoGeometry.Canonical.PrimeMBKSelfAdjointTrace
