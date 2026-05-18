import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Canonical.ZetaFunctionalEquationDualitySocket

/-!
# InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge

Calibration bridge between the self-concordant zeta barrier and the zeta-period
carrier.

This file does not prove a new analytic theorem. It packages the native
barrier owner together with the zeta-period socket and records the missing
bridge as explicit bridge data:

* the zeta period is identified with the barrier readout;
* the barrier-critical certificate is supplied;
* the critical line follows by the existing barrier owner theorem.

No RH claim is added here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Canonical.ZetaFunctionalEquationDualitySocket

/--
Calibration packet tying the self-concordant barrier owner to the zeta-period
carrier.

`zetaPeriod_eq_xi` is the bridge identifying the zeta-period readout with the
barrier `xi` readout.
`zeros_are_barrier_critical` is the supplied barrier-critical certificate.
-/
@[rep_depth operator]
structure SelfConcordantZetaBarrierZetaPeriodCalibrationPacket where
  barrier : VariationalRHTarget
  brane : FunctionalEquationZetaBraneSocket
  zetaPeriod_eq_xi :
    ∀ s : ℂ,
      brane.brane.centralCharge.zetaPeriod s = barrier.xi s
  zeros_are_barrier_critical :
    barrier.zeros_are_barrier_critical

variable (C : SelfConcordantZetaBarrierZetaPeriodCalibrationPacket)

/-- Reexport of the supplied barrier-critical bridge. -/
@[bridge_target_tag, rep_depth operator]
theorem zeros_are_barrier_critical_law :
    C.barrier.zeros_are_barrier_critical :=
  C.zeros_are_barrier_critical

/--
The calibrated zeta period forces the critical line once the supplied
barrier-critical bridge is present.
-/
@[bridge_target_tag, rep_depth operator]
theorem zetaPeriod_zero_implies_criticalLine
    (s : ℂ)
    (hz : C.brane.brane.centralCharge.zetaPeriod s = 0) :
    OnCriticalLine s := by
  have hxi : C.barrier.xi s = 0 := by
    simpa [C.zetaPeriod_eq_xi s] using hz
  exact SelfConcordantZetaBarrier.variationalRH_implies_criticalLine
    C.barrier C.zeros_are_barrier_critical s hxi

end InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge
