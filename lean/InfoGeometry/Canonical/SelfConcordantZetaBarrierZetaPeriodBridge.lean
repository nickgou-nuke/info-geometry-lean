import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Canonical.CantorDiracZetaBraneSocket
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.SelfConcordantZetaBarrier

/-!
# Zeta-period zero-location transport

This module contains the direct substitution theorem formerly hidden behind a
calibration packet.  It assumes an actual equality of functions and an actual
zero-location theorem; no carrier, socket, or evidence field is constructed.
-/

namespace InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/--
If a zeta-period function equals a function whose zeros lie on the critical
line, then every zeta-period zero lies on the critical line.
-/
@[bridge_target_tag, rep_depth operator]
theorem zetaPeriod_zero_implies_criticalLine
    (zetaPeriod xi : ℂ → ℂ)
    (zetaPeriod_eq_xi : zetaPeriod = xi)
    (xi_zero_on_criticalLine :
      ∀ s : ℂ, xi s = 0 → OnCriticalLine s)
    (s : ℂ)
    (hz : zetaPeriod s = 0) :
    OnCriticalLine s := by
  apply xi_zero_on_criticalLine s
  simpa [zetaPeriod_eq_xi] using hz

open InfoGeometry.Canonical.CantorDiracZetaBraneSocket
open InfoGeometry.Canonical.SelfConcordantZetaBarrier

/--
Typed owner-level form of the former calibration packet: identification of a
concrete Cantor--Dirac brane period with the xi function of a variational
barrier transports the barrier's proved zero-location theorem.
-/
@[bridge_target_tag, rep_depth operator]
theorem braneZetaPeriod_zero_implies_criticalLine
    (barrier : VariationalRHTarget)
    (brane : CantorDiracSYZZetaBraneConjectureSocket)
    (zetaPeriod_eq_xi :
      ∀ z : ℂ, brane.centralCharge z = barrier.xi z)
    (s : ℂ)
    (hz : brane.centralCharge s = 0) :
    OnCriticalLine s := by
  apply variationalRH_implies_criticalLine barrier s
  simpa [zetaPeriod_eq_xi s] using hz

end InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge
