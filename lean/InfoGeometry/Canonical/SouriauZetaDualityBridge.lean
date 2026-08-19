import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-! Typed conditional bridge from supplied zero data to a finite barrier. -/

noncomputable section

namespace InfoGeometry.Canonical.SouriauZetaDualityBridge

open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Vanishing of the readout implies the supplied finite-barrier inequality. -/
@[rep_depth thermo]
theorem zeros_are_barrier_critical
    (xi : ℂ → ℂ)
    (isSurprisalSingularity : ℂ → Prop)
    (surprisal_singularity_iff_zero :
      ∀ s, isSurprisalSingularity s ↔ xi s = 0)
    (duality_singularity_to_minimum :
      ∀ s, isSurprisalSingularity s →
        ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) → ∀ σ : ℝ,
          primeSpectralBarrier S s.re ≤ primeSpectralBarrier S σ)
    (s₀ : ℂ) (hz : xi s₀ = 0)
    (S : Finset ℕ) (_hS : ∀ p ∈ S, 1 < p) (σ : ℝ) :
    primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ := by
  have hSingularity : isSurprisalSingularity s₀ :=
    (surprisal_singularity_iff_zero s₀).mpr hz
  exact duality_singularity_to_minimum s₀ hSingularity S _hS σ

/-- The supplied barrier target implies the critical-line predicate. -/
@[rep_depth thermo]
theorem RH_of_SouriauDuality
    (xi : ℂ → ℂ)
    (isSurprisalSingularity : ℂ → Prop)
    (surprisal_singularity_iff_zero :
      ∀ s, isSurprisalSingularity s ↔ xi s = 0)
    (duality_singularity_to_minimum :
      ∀ s, isSurprisalSingularity s →
        ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) → ∀ σ : ℝ,
          primeSpectralBarrier S s.re ≤ primeSpectralBarrier S σ)
    (s₀ : ℂ) (hz : xi s₀ = 0) :
    OnCriticalLine s₀ := by
  apply variationalRH_implies_criticalLine xi
  · intro s hz' S hS σ
    exact zeros_are_barrier_critical xi isSurprisalSingularity
      surprisal_singularity_iff_zero duality_singularity_to_minimum
      s hz' S hS σ
  · exact hz

end InfoGeometry.Canonical.SouriauZetaDualityBridge
