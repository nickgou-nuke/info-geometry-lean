import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Canonical.SelfConcordantZetaBarrier
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# InfoGeometry.Canonical.SouriauZetaDualityBridge

Conditional Souriau/Legendre zeta-duality hypotheses and debt lemmas.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauZetaDualityBridge

open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/--
Explicit hypotheses for the Souriau-Legendre zeta-barrier debt lemma.
-/
@[rep_depth thermo]
structure SouriauZetaDualityHypotheses where
  /-- The completed Riemann xi function. -/
  xi : ℂ → ℂ

  /-- The functional equation for the supplied xi function. -/
  xi_reflection : ∀ s, xi s = xi (1 - s)

  /-- The primal surprisal potential, nominally `-log |ξ(s)|`. -/
  surprisal : ℂ → ℝ

  /-- Supplied analytic predicate: `s` is a singularity of the surprisal. -/
  isSurprisalSingularity : ℂ → Prop

  /-- The singularities of the surprisal potential are exactly the zeros of `ξ`. -/
  surprisal_singularity_iff_zero :
    ∀ s : ℂ, isSurprisalSingularity s ↔ xi s = 0

  /--
  Conditional Legendre-duality bridge: a supplied singularity maps to a global
  minimum of every finite prime spectral barrier.
  -/
  duality_singularity_to_minimum :
    ∀ s : ℂ, isSurprisalSingularity s →
      ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, 1 < p) (σ : ℝ),
        primeSpectralBarrier S s.re ≤ primeSpectralBarrier S σ

  /-- Guardrail: this packet is architectural/conditional, not an unconditional RH proof. -/
  no_unconditional_RH_claim_guard : Type*

namespace SouriauZetaDualityHypotheses

variable (D : SouriauZetaDualityHypotheses)

/--
Debt lemma: under the explicit duality hypotheses, zeros of `ξ` minimize the finite prime barrier.
-/
@[bridge_target_tag, rep_depth thermo]
theorem zeros_are_barrier_critical
    (s₀ : ℂ) (hz : D.xi s₀ = 0)
    (S : Finset ℕ) (_hS : ∀ p ∈ S, 1 < p) (σ : ℝ) :
    primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ := by
  have hSingularity : D.isSurprisalSingularity s₀ :=
    (D.surprisal_singularity_iff_zero s₀).mpr hz
  exact D.duality_singularity_to_minimum s₀ hSingularity S _hS σ

/-- Construct the variational RH target from the supplied conditional hypotheses. -/
@[bridge_target_tag, rep_depth operator]
def toVariationalRHTarget : VariationalRHTarget where
  xi := D.xi
  xi_reflection := D.xi_reflection
  barrierApproximation := fun _ => ∅
  approx_primes := fun _ _ h => by simp at h
  zeros_are_barrier_critical :=
    (∀ s₀ : ℂ, D.xi s₀ = 0 →
      ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) →
        ∀ σ : ℝ,
          primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ)
  zeros_are_barrier_critical_shape := rfl
  no_unconditional_RH_claim_guard := D.no_unconditional_RH_claim_guard

/--
Debt lemma: if the supplied duality hypotheses hold for `D`, then any zero of the supplied `xi` lies on the critical line.
-/
@[bridge_target_tag, rep_depth thermo]
theorem RH_of_SouriauDuality
    (s₀ : ℂ) (hz : D.xi s₀ = 0) :
    OnCriticalLine s₀ := by
  have hBridge : D.toVariationalRHTarget.zeros_are_barrier_critical := by
    intro s hs S hS σ
    exact D.zeros_are_barrier_critical s hs S hS σ
  exact variationalRH_implies_criticalLine D.toVariationalRHTarget hBridge s₀ hz

end SouriauZetaDualityHypotheses

end InfoGeometry.Canonical.SouriauZetaDualityBridge
