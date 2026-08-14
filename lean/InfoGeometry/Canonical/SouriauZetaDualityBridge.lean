import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-! Typed conditional bridge from supplied zero data to a finite barrier. -/

noncomputable section

namespace InfoGeometry.Canonical.SouriauZetaDualityBridge

open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- A supplied zero readout together with its finite-barrier realization. -/
@[rep_depth thermo]
structure SouriauZetaDualityHypotheses where
  /-- The supplied complex-valued readout. -/
  xi : ℂ → ℂ

  /-- Reflection symmetry of the supplied readout. -/
  xi_reflection : ∀ s, xi s = xi (1 - s)

  /-- A real-valued potential attached to the readout. -/
  surprisal : ℂ → ℝ

  /-- Predicate identifying the supplied singular points. -/
  isSurprisalSingularity : ℂ → Prop

  /-- The singular predicate agrees with vanishing of the readout. -/
  surprisal_singularity_iff_zero :
    ∀ s : ℂ, isSurprisalSingularity s ↔ xi s = 0

  /-- A supplied singularity minimizes every selected finite barrier. -/
  duality_singularity_to_minimum :
    ∀ s : ℂ, isSurprisalSingularity s →
      ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, 1 < p) (σ : ℝ),
        primeSpectralBarrier S s.re ≤ primeSpectralBarrier S σ


namespace SouriauZetaDualityHypotheses

variable (D : SouriauZetaDualityHypotheses)

/-- Vanishing of the readout implies the supplied finite-barrier inequality. -/
@[bridge_target_tag, rep_depth thermo]
theorem zeros_are_barrier_critical
    (s₀ : ℂ) (hz : D.xi s₀ = 0)
    (S : Finset ℕ) (_hS : ∀ p ∈ S, 1 < p) (σ : ℝ) :
    primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ := by
  have hSingularity : D.isSurprisalSingularity s₀ :=
    (D.surprisal_singularity_iff_zero s₀).mpr hz
  exact D.duality_singularity_to_minimum s₀ hSingularity S _hS σ

/-- Package the supplied data in the variational target structure. -/
@[bridge_target_tag, rep_depth operator]
def toVariationalRHTarget : VariationalRHTarget where
  xi := D.xi
  xi_reflection := D.xi_reflection
  barrierApproximation := fun _ => ∅
  approx_primes := fun _ _ h => by simp at h
  zeros_are_barrier_critical := fun s₀ hz S hS σ =>
    D.zeros_are_barrier_critical s₀ hz S hS σ

/-- The supplied barrier target implies the critical-line predicate. -/
@[bridge_target_tag, rep_depth thermo]
theorem RH_of_SouriauDuality
    (s₀ : ℂ) (hz : D.xi s₀ = 0) :
    OnCriticalLine s₀ := by
  exact variationalRH_implies_criticalLine D.toVariationalRHTarget s₀ hz

end SouriauZetaDualityHypotheses

end InfoGeometry.Canonical.SouriauZetaDualityBridge
