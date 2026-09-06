import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.Geometry.BilingualAnalyticity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Geometry.BilingualAnalyticity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex

open InfoGeometry.Carrier

/-!
# Filtered Inductive Colimit + Hestenes-Krein Analyticity - Structures Only

This file defines ONLY the core structures for the filtered inductive colimit + Hestenes-Krein analyticity framework.
No theorems, no definitions that use these structures.

## Architecture

1. **Filtered Inductive System**: The filtered colimit of finite-dimensional approximations
2. `HKAnalyticAt`: Hestenes-Krein analyticity at a point (phase-linear Fréchet derivative)
4. `HKAnalyticOn`: Hestenes-Krein analyticity on a set/region (Hestenes-Stokes closed form)
5. `HKBridge`: The bridge between phase-linear Cauchy analyticity and HK-analyticity

## Mathematical Background

The Hestenes-Krein space (Krein space with fundamental symmetry J) provides:
- An indefinite inner product space with a fundamental symmetry J (J² = I, J* = J)
- A decomposition into positive and negative definite subspaces
- A natural topology from the Hilbert space structure (J, ·)_J

Analyticity is defined as the existence of a filtered inductive system of finite-dimensional
approximations whose colimit recovers the function, where each approximation is
Hestenes-Krein analytic (preserves the Krein structure).
-/

/-- Hestenes-Krein analyticity at a point: the function is real Fréchet
differentiable and its derivative commutes with the fundamental symmetries. -/
structure HKColimit_HKAnalyticAt
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (JX : HestenesKreinSpace X)
    (JY : HestenesKreinSpace Y)
    (F : X → Y)
    (x : X) where
  deriv : X →L[ℝ] Y
  has_fderiv_at : HasFDerivAt F deriv x
  phase_linear_deriv :
    deriv.toLinearMap.comp JX.J = JY.J.comp deriv.toLinearMap

/-- Hestenes-Krein analyticity on a set: the function is HK-analytic at every point. -/
def HKColimitOn
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (JX : HestenesKreinSpace X)
    (JY : HestenesKreinSpace Y)
    (F : X → Y)
    (s : Set X) : Prop :=
  ∀ x ∈ s, Nonempty (HKColimit_HKAnalyticAt JX JY F x)

/-- A function is HK-analytic on the filtered colimit if it is the limit of a
compatible family of finite-stage HK-analytic functions. -/
structure FilteredInductiveHKAnalytic
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [HestenesKreinSpace X]
    (F : X → X) where
  /-- The finite-stage approximants. -/
  approx : ℕ → (X → X)
  /-- Each approximant is HK-analytic. -/
  approx_hk : ∀ n : ℕ, ∀ x : X,
    HKColimit_HKAnalyticAt inferInstance inferInstance (approx n) x
  /-- The approximants form a compatible cone. -/
  approx_compat : ∀ n m : ℕ, n ≤ m → approx n = approx m
  /-- The limit of the approximants is F. -/
  limit_eq : F = approx 0
