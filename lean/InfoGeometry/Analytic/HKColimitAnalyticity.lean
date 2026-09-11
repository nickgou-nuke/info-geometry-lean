import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredDirectLimitOperatorUniqueness
import InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Analytic.HKColimitStructures
import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.Geometry.BilingualAnalyticity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Geometry.BilingualAnalyticity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex

noncomputable section

namespace InfoGeometry.Analytic.HKColimitAnalyticity

open InfoGeometry.Canonical.FilteredDirectLimitOperator

universe u

variable
    (Stage : ℕ → Type u)
    [∀ n, AddCommGroup (Stage n)]
    (f : ∀ m n : ℕ, m ≤ n → Stage m →+ Stage n)

/-- Compatible finite Hestenes-Krein phases with `Jₙ² = -I`. -/
structure FilteredKreinPhaseFamily
    extends CompatibleOperatorFamily Stage f where
  phase_sq : ∀ n x, op n (op n x) = -x

namespace FilteredKreinPhaseFamily

variable (J : FilteredKreinPhaseFamily Stage f)

/-- Native additive operator induced on Mathlib's direct limit. -/
def directLimitPhase :
    AddCommGroup.DirectLimit Stage f →+
      AddCommGroup.DirectLimit Stage f :=
  CompatibleOperatorFamily.directLimitOperator
    Stage f J.toCompatibleOperatorFamily

@[simp]
theorem directLimitPhase_of (n : ℕ) (x : Stage n) :
    directLimitPhase Stage f J (AddCommGroup.DirectLimit.of Stage f n x) =
      AddCommGroup.DirectLimit.of Stage f n (J.op n x) :=
  CompatibleOperatorFamily.directLimitOperator_of
    Stage f J.toCompatibleOperatorFamily n x

/-- The finite phase-square law survives the filtered direct limit. -/
theorem directLimitPhase_sq_apply
    (z : AddCommGroup.DirectLimit Stage f) :
    directLimitPhase Stage f J (directLimitPhase Stage f J z) = -z := by
  refine AddCommGroup.DirectLimit.induction_on z ?_
  intro n x
  rw [directLimitPhase_of, directLimitPhase_of, J.phase_sq]
  exact (AddCommGroup.DirectLimit.of Stage f n).map_neg x

/-- The descended phase has trivial kernel. -/
theorem directLimitPhase_eq_zero_iff
    (z : AddCommGroup.DirectLimit Stage f) :
    directLimitPhase Stage f J z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h := congrArg (directLimitPhase Stage f J) hz
    rw [directLimitPhase_sq_apply, map_zero] at h
    exact neg_eq_zero.mp h
  · rintro rfl
    exact map_zero (directLimitPhase Stage f J)

/-- The native descended Hestenes-Krein phase is injective. -/
theorem directLimitPhase_injective :
    Function.Injective (directLimitPhase Stage f J) := by
  intro x y hxy
  have h := congrArg (directLimitPhase Stage f J) hxy
  simpa only [directLimitPhase_sq_apply, neg_inj] using h

end FilteredKreinPhaseFamily

end InfoGeometry.Analytic.HKColimitAnalyticity

open InfoGeometry.Carrier

/-!
# Filtered Inductive Colimit + Hestenes-Krein Analyticity

This module replaces the `CauchyAnalyticAt`/`AnalyticAt` approach with a
**filtered inductive colimit + Hestenes-Krein analyticity** framework.

## Architecture

1. **Filtered Inductive System**: The filtered colimit of finite-dimensional approximations
2. `HKAnalyticAt`: Hestenes-Krein analyticity at a point (phase-linear Fréchet derivative)
3. `FilteredInductiveLimit`: The colimit of the filtered system via `FilteredDirectLimitOperator`
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

open InfoGeometry.Carrier

namespace InfoGeometry.Analytic.HKColimit

open InfoGeometry.Carrier

/-- The derivative is phase-linear with respect to the fundamental symmetries. -/
theorem deriv_phaseLinear {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {JX : HestenesKreinSpace X} {JY : HestenesKreinSpace Y} {F : X → Y} {x : X} (A : HKColimit_HKAnalyticAt (JX := inferInstance) (JY := inferInstance) F x) :
    A.deriv.toLinearMap.comp JX.J = JY.J.comp A.deriv.toLinearMap :=
  A.phase_linear_deriv

/-- Pointwise Cauchy-Riemann law. -/
theorem HKColimit_cauchyRiemann_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {JX : HestenesKreinSpace X} {JY : HestenesKreinSpace Y} {F : X → Y} {x : X} (A : HKColimit_HKAnalyticAt (inferInstance : HestenesKreinSpace X) (inferInstance : HestenesKreinSpace Y) F x) (v : X) : A.deriv (JX.J v) = JY.J (A.deriv v) := by
  exact LinearMap.congr_fun A.phase_linear_deriv v

/-- Construct HKAnalyticAt from a continuous linear map that is phase-linear. -/
def HKColimit_HKAnalyticAt.ofContinuousLinearMap
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {JX : HestenesKreinSpace X}
    {JY : HestenesKreinSpace Y}
    (L : X →L[ℝ] Y)
    (hL : L.toLinearMap.comp JX.J = JY.J.comp L.toLinearMap)
    (x : X) :
    HKColimit_HKAnalyticAt (inferInstance : HestenesKreinSpace X) (inferInstance : HestenesKreinSpace Y) (fun y : X => L y) x :=
  ⟨L, by simpa using L.hasFDerivAt, hL⟩

/-- The identity map is HK-analytic. -/
def HKAnalyticAt_id
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {JX : HestenesKreinSpace X}
    (x : X) :
    HKColimit_HKAnalyticAt (inferInstance : HestenesKreinSpace X) (inferInstance : HestenesKreinSpace X) (fun y : X => y) x :=
  ⟨ContinuousLinearMap.id ℝ X, by simpa using (ContinuousLinearMap.id ℝ X).hasFDerivAt, by
    ext v
    rfl⟩

/-- Compatibility alias for the imported owner of HK-analyticity on a set. -/
abbrev HKColimitOn
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (JX : HestenesKreinSpace X)
    (JY : HestenesKreinSpace Y)
    (F : X → Y)
    (s : Set X) : Prop :=
  _root_.HKColimitOn JX JY F s

/-- Compatibility alias for the imported filtered-inductive analyticity owner. -/
abbrev FilteredInductiveHKAnalytic
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [HestenesKreinSpace X]
    (F : X → X) :=
  _root_.FilteredInductiveHKAnalytic F

/-- A filtered family whose limit is its zeroth stage is HK-analytic everywhere. -/
theorem hkAnalyticOn_univ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [HestenesKreinSpace X] {F : X → X} (A : FilteredInductiveHKAnalytic F) :
    HKColimitOn inferInstance inferInstance F Set.univ := by
  intro x _
  refine ⟨?_⟩
  rw [A.limit_eq]
  exact A.approx_hk 0 x
