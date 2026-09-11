import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Canonical.OperatorJKOStep

/-!
# JKO objective transport on a Hestenes--Krein colimit

This owner transports a supplied finite-stage energy/penalty objective through
the canonical maps of a filtered Hestenes--Krein cone.  It does not construct
an argmin, a Wasserstein space, a heat flow, or a continuous-time limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinJKOColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Krein

def stageObjective
    {C : HestenesKreinCone}
    (energy : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (penalty : ∀ n, ℝ → DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (τ : ℝ) (n : ℕ)
    (previous next : DoubledSpace (C.Base n)) : ℝ :=
  energy n next + penalty n τ next previous

def limitObjective
    {C : HestenesKreinCone}
    (energy : DoubledSpace C.LimitBase → ℝ)
    (penalty : ℝ → DoubledSpace C.LimitBase → DoubledSpace C.LimitBase → ℝ)
    (τ : ℝ) (previous next : DoubledSpace C.LimitBase) : ℝ :=
  energy next + penalty τ next previous

theorem stageObjective_eq_limitObjective
    {C : HestenesKreinCone}
    (energy : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitEnergy : DoubledSpace C.LimitBase → ℝ)
    (penalty : ∀ n, ℝ → DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (limitPenalty : ℝ → DoubledSpace C.LimitBase → DoubledSpace C.LimitBase → ℝ)
    (henergy : ∀ n x, energy n x = limitEnergy (C.ι n x))
    (hpenalty : ∀ n τ x y,
      penalty n τ x y = limitPenalty τ (C.ι n x) (C.ι n y))
    (τ : ℝ) (n : ℕ)
    (previous next : DoubledSpace (C.Base n)) :
    stageObjective energy penalty τ n previous next =
      limitObjective limitEnergy limitPenalty τ (C.ι n previous) (C.ι n next) := by
  unfold stageObjective limitObjective
  rw [henergy n next, hpenalty n τ next previous]

theorem stageObjective_minimizing_to_limit
    {C : HestenesKreinCone}
    (energy : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitEnergy : DoubledSpace C.LimitBase → ℝ)
    (penalty : ∀ n, ℝ → DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (limitPenalty : ℝ → DoubledSpace C.LimitBase → DoubledSpace C.LimitBase → ℝ)
    (henergy : ∀ n x, energy n x = limitEnergy (C.ι n x))
    (hpenalty : ∀ n τ x y,
      penalty n τ x y = limitPenalty τ (C.ι n x) (C.ι n y))
    (τ : ℝ) (n : ℕ)
    (previous next : DoubledSpace (C.Base n))
    (hmin : ∀ candidate : DoubledSpace (C.Base n),
      stageObjective energy penalty τ n previous next ≤
        stageObjective energy penalty τ n previous candidate) :
    ∀ candidate : DoubledSpace (C.Base n),
      limitObjective limitEnergy limitPenalty τ (C.ι n previous) (C.ι n next) ≤
        limitObjective limitEnergy limitPenalty τ (C.ι n previous) (C.ι n candidate) := by
  intro candidate
  rw [← stageObjective_eq_limitObjective energy limitEnergy penalty limitPenalty
    henergy hpenalty τ n previous next]
  rw [← stageObjective_eq_limitObjective energy limitEnergy penalty limitPenalty
    henergy hpenalty τ n previous candidate]
  exact hmin candidate

theorem stageObjective_bondIterate_eq
    {C : HestenesKreinCone}
    (energy : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (penalty : ∀ n, ℝ → DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (henergy : ∀ n m x,
      energy (n + m) (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) = energy n x)
    (hpenalty : ∀ n m τ x y,
      penalty (n + m) τ
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x)
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m y) = penalty n τ x y)
    (τ : ℝ) (n m : ℕ)
    (previous next : DoubledSpace (C.Base n)) :
    stageObjective energy penalty τ (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m previous)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m next) =
      stageObjective energy penalty τ n previous next := by
  unfold stageObjective
  rw [henergy n m next, hpenalty n m τ next previous]

end InfoGeometry.Canonical.HestenesKreinJKOColimit

end noncomputable section
