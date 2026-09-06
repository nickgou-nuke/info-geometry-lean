import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CantorDiracZetaBrane
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.SelfConcordantZetaBarrier

/-!
# Zeta-period zero-location transport

This module contains the direct substitution theorem formerly hidden behind a
calibration packet.  It assumes an actual equality of functions and an actual
zero-location theorem; no carrier, interface, or evidence field is constructed.
-/

namespace InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/--
If a zeta-period function equals a function whose zeros lie on the critical
line, then every zeta-period zero lies on the critical line.
-/
@[rep_depth operator]
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

open InfoGeometry.Canonical.CantorDiracZetaBrane
open InfoGeometry.Canonical.SelfConcordantZetaBarrier

/--
Typed owner-level form of the former calibration packet: identification of a
concrete Cantor--Dirac brane period with the xi function of a variational
barrier transports the barrier's proved zero-location theorem.
-/
@[rep_depth operator]
theorem braneZetaPeriod_zero_implies_criticalLine
    (xi : ℂ → ℂ)
    (zeros_are_barrier_critical :
      ∀ s₀ : ℂ, xi s₀ = 0 →
        ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) → ∀ σ : ℝ,
          primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ)
    (centralCharge : ℂ → ℂ)
    (zetaPeriod_eq_xi :
      ∀ z : ℂ, centralCharge z = xi z)
    (s : ℂ)
    (hz : centralCharge s = 0) :
    OnCriticalLine s := by
  apply variationalRH_implies_criticalLine xi zeros_are_barrier_critical s
  simpa [zetaPeriod_eq_xi s] using hz

end InfoGeometry.Canonical.SelfConcordantZetaBarrierZetaPeriodBridge
