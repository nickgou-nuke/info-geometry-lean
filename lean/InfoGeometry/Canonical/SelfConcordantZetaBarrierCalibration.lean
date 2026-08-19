import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Meta.Architecture

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

/-- Reexport of the supplied barrier-critical bridge. -/
@[rep_depth operator]
theorem zeros_are_barrier_critical
    (xi : ℂ → ℂ)
    (zeros_are_barrier_critical :
      ∀ s₀ : ℂ, xi s₀ = 0 →
        ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) → ∀ σ : ℝ,
          primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ)
    (s₀ : ℂ) (hz : xi s₀ = 0)
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) (σ : ℝ) :
    primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ :=
  zeros_are_barrier_critical s₀ hz S hS σ

/--
The calibrated barrier still forces the critical line once the supplied
bridge property is present.
-/
@[rep_depth operator]
theorem criticalLine_of_calibration
    (xi : ℂ → ℂ)
    (zeros_are_barrier_critical :
      ∀ s₀ : ℂ, xi s₀ = 0 →
        ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) → ∀ σ : ℝ,
          primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ)
    (s₀ : ℂ)
    (hz : xi s₀ = 0) :
    OnCriticalLine s₀ := by
  exact SelfConcordantZetaBarrier.variationalRH_implies_criticalLine
    xi zeros_are_barrier_critical s₀ hz

end InfoGeometry.Canonical.SelfConcordantZetaBarrierCalibration
