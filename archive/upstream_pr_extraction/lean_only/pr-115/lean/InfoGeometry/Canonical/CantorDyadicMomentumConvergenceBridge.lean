import Mathlib.Tactic
import InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge

/-!
# Cantor dyadic momentum convergence contract

This owner records the precise data needed for a genuine continuum momentum
theorem.  It is intentionally not an existence theorem: concrete Cantor
operators, a common core, and their convergence must be supplied by a later
analytic construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorDyadicMomentumConvergenceBridge

abbrev MomentumIndex := Fin 4

def CoreConvergenceStatement
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (core : Set H) (approximants : MomentumIndex → ℕ → H → H)
    (generators : MomentumIndex → H →L[ℂ] H) : Prop :=
  ∀ μ ψ, ψ ∈ core →
    Filter.Tendsto (fun n => approximants μ n ψ) Filter.atTop
      (nhds (generators μ ψ))

structure MomentumConvergenceDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] where
  core : Set H
  approximants : MomentumIndex → ℕ → H → H
  generators : MomentumIndex → H →L[ℂ] H
  convergence : CoreConvergenceStatement core approximants generators
  commuting : ∀ μ ν,
    (generators μ).comp (generators ν) =
      (generators ν).comp (generators μ)

theorem MomentumConvergenceDatum.tendsto
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (datum : MomentumConvergenceDatum H) (μ : MomentumIndex)
    {ψ : H} (hψ : ψ ∈ datum.core) :
    Filter.Tendsto (fun n => datum.approximants μ n ψ) Filter.atTop
      (nhds (datum.generators μ ψ)) :=
  datum.convergence μ ψ hψ

theorem MomentumConvergenceDatum.commuting_generators
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (datum : MomentumConvergenceDatum H) (μ ν : MomentumIndex) :
    (datum.generators μ).comp (datum.generators ν) =
      (datum.generators ν).comp (datum.generators μ) :=
  datum.commuting μ ν

end InfoGeometry.Canonical.CantorDyadicMomentumConvergenceBridge
