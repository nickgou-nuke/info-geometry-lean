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
barrier owner together with the zeta-period socket and records only the readout
identification between the two.  The barrier-critical theorem remains an
explicit input to the downstream implication; it is not hidden in this packet.

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
barrier `xi` readout.  No barrier-critical proof is stored in this packet.
-/
@[rep_depth operator]
structure SelfConcordantZetaBarrierZetaPeriodCalibrationPacket where
  barrier : VariationalRHTarget
  brane : FunctionalEquationZetaBraneSocket
  zetaPeriod_eq_xi :
    ∀ s : ℂ,
      brane.brane.centralCharge.zetaPeriod s = barrier.xi s

variable (C : SelfConcordantZetaBarrierZetaPeriodCalibrationPacket)

/--
The calibrated zeta period forces the critical line once an actual
barrier-critical theorem for the barrier owner is supplied.
-/
@[bridge_target_tag, rep_depth operator]
theorem zetaPeriod_zero_implies_criticalLine
    (hcritical : C.barrier.zeros_are_barrier_critical)
    (s : ℂ)
    (hz : C.brane.brane.centralCharge.zetaPeriod s = 0) :
    OnCriticalLine s := by
  have hxi : C.barrier.xi s = 0 := by
    simpa [C.zetaPeriod_eq_xi s] using hz
  exact SelfConcordantZetaBarrier.variationalRH_implies_criticalLine
    C.barrier hcritical s hxi

end InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge
