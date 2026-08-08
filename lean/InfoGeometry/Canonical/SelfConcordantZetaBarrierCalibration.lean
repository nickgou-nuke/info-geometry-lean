import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget

/-!
# InfoGeometry.Canonical.SelfConcordantZetaBarrierCalibration

Thin calibration wrapper for the self-concordant zeta barrier.

This file does not prove a new variational theorem.  It packages the existing
`SelfConcordantZetaBarrier.VariationalRHTarget` with an explicit property for
the missing bridge `zeros_are_barrier_critical`, and reexports the owner
theorem `variationalRH_implies_criticalLine`.

The intent is architectural: keep the self-concordant barrier as the native
optimization owner, and keep the zeta-period zero-to-barrier-critical bridge as
the supplied calibration datum.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfConcordantZetaBarrierCalibration

open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/--
Calibration packet connecting the self-concordant barrier owner to the missing
variational bridge.

`barrier` is the owner-side variational target.
`zeros_are_barrier_critical` is the explicit supplied bridge property.
-/
@[rep_depth operator]
abbrev SelfConcordantZetaBarrierCalibrationPacket := VariationalRHTarget

namespace SelfConcordantZetaBarrierCalibrationPacket

abbrev barrier (C : SelfConcordantZetaBarrierCalibrationPacket) :
    VariationalRHTarget := C

end SelfConcordantZetaBarrierCalibrationPacket

variable (C : SelfConcordantZetaBarrierCalibrationPacket)

/-- Reexport of the supplied barrier-critical bridge. -/
@[bridge_target_tag, rep_depth operator]
theorem zeros_are_barrier_critical
    (s₀ : ℂ) (hz : C.barrier.xi s₀ = 0)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) (σ : ℝ) :
    primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ :=
  C.barrier.zeros_are_barrier_critical s₀ hz S hS σ

/--
The calibrated barrier still forces the critical line once the supplied
bridge property is present.
-/
@[bridge_target_tag, rep_depth operator]
theorem criticalLine_of_calibration
    (s₀ : ℂ)
    (hz : C.barrier.xi s₀ = 0) :
    OnCriticalLine s₀ := by
  exact SelfConcordantZetaBarrier.variationalRH_implies_criticalLine
    C.barrier s₀ hz

end InfoGeometry.Canonical.SelfConcordantZetaBarrierCalibration
