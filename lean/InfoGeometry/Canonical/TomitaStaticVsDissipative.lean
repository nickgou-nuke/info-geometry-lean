import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.TomitaStaticVsDissipative

Finite theorem corridor separating:

* equilibrium Tomita-style invariance (static potential along flow),
* dissipative semigroup-style monotonic potential law.

No Type III completion is claimed here; this is a finite structural interface.
-/

namespace InfoGeometry.Canonical.TomitaStaticVsDissipative

/-! ## Equilibrium (static) side -/

structure TomitaEquilibrium (StateSpace : Type*) where
  modularPotential : StateSpace → ℝ
  flow : ℝ → StateSpace → StateSpace
  flowInvariant : ∀ (t : ℝ) (ρ : StateSpace),
    modularPotential (flow t ρ) = modularPotential ρ

/--
Along a pure Tomita-equilibrium trajectory, the modular potential has
zero derivative (it is constant in time).
-/
theorem tomita_is_static
    {S : Type*} (env : TomitaEquilibrium S) (ρ : S) (t : ℝ) :
    HasDerivAt (fun time => env.modularPotential (env.flow time ρ)) 0 t := by
  have hconst :
      (fun time => env.modularPotential (env.flow time ρ))
        = (fun _ => env.modularPotential ρ) := by
    ext time
    exact env.flowInvariant time ρ
  rw [hconst]
  simpa using (hasDerivAt_const t (env.modularPotential ρ))

theorem tomita_potential_eq_initial
    {S : Type*} (env : TomitaEquilibrium S) (ρ : S) (t : ℝ) :
    env.modularPotential (env.flow t ρ) = env.modularPotential ρ :=
  env.flowInvariant t ρ

/-! ## Dissipative (monotone) side -/

structure DissipativeFlow (StateSpace : Type*) where
  potential : StateSpace → ℝ
  flow : ℝ → StateSpace → StateSpace
  /-- Normalization at time zero. -/
  flowZero : flow 0 = id
  /-- Semigroup law on nonnegative times (forward direction only). -/
  flowSemigroup :
    ∀ {t s : ℝ}, 0 ≤ t → 0 ≤ s →
      flow (t + s) = fun ρ => flow t (flow s ρ)
  /-- Monotone potential law (finite entropy-production interface). -/
  potentialMonotone :
    ∀ {t₂ t₁ : ℝ} {ρ : StateSpace}, 0 ≤ t₁ → t₁ ≤ t₂ →
      potential (flow t₂ ρ) ≤ potential (flow t₁ ρ)

theorem dissipative_potential_nonincreasing_from_zero
    {S : Type*} (D : DissipativeFlow S) (ρ : S) {t : ℝ}
    (ht : 0 ≤ t) :
    D.potential (D.flow t ρ) ≤ D.potential ρ := by
  have h := D.potentialMonotone (ρ := ρ) (t₁ := 0) (t₂ := t) (by positivity) ht
  simpa [D.flowZero] using h

end InfoGeometry.Canonical.TomitaStaticVsDissipative
