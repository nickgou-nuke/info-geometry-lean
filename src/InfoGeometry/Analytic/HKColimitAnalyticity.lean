/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

/-- Concrete symplectic/quarter-turn rotation `(a, b) ↦ (-b, a)` on `ℤ × ℤ` satisfying `J² = -I`. -/
def intPlaneQuarterTurn : (ℤ × ℤ) →+ (ℤ × ℤ) where
  toFun p := (-p.2, p.1)
  map_zero' := by simp
  map_add' p q := by
    ext <;> simp [add_comm]

theorem intPlaneQuarterTurn_sq (p : ℤ × ℤ) :
    intPlaneQuarterTurn (intPlaneQuarterTurn p) = -p := by
  cases p
  rfl

/-- Canonical constructive inhabitant of `FilteredKreinPhaseFamily` over `Stage n = ℤ × ℤ`. -/
def canonicalIntPlanePhaseFamily :
    FilteredKreinPhaseFamily (fun _ => ℤ × ℤ) (fun _ _ _ => AddMonoidHom.id (ℤ × ℤ)) where
  op _ := intPlaneQuarterTurn
  commutes _ _ _ _ := rfl
  phase_sq _ p := intPlaneQuarterTurn_sq p

end InfoGeometry.Analytic.HKColimitAnalyticity

/-!
# Filtered Inductive Colimit + Hestenes-Krein Analyticity

This module unites:
1. **Filtered Direct-Limit Krein Phase Transport (`Sense D` / `M1`)**:
   `FilteredKreinPhaseFamily` descending finite-stage phase operators $J_n^2 = -I$ to
   `AddCommGroup.DirectLimit Stage f` (`directLimitPhase_sq_apply`, `directLimitPhase_injective`).
2. **Pointwise Phase-Linear Fréchet Differentiability (`Sense B` / `M2`)**:
   `HKColimit_HKAnalyticAt` (`deriv_phaseLinear`, `HKColimit_cauchyRiemann_apply`,
   `HKColimit_HKAnalyticAt.ofContinuousLinearMap`, `HKAnalyticAt_id`).
-/

namespace InfoGeometry.Analytic.HKColimit

open InfoGeometry.Carrier

/-- The derivative is phase-linear with respect to the fundamental symmetries. -/
theorem deriv_phaseLinear
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {JX : HestenesKreinSpace X} {JY : HestenesKreinSpace Y}
    {F : X → Y} {x : X}
    (A : HKColimit_HKAnalyticAt (JX := inferInstance) (JY := inferInstance) F x) :
    A.deriv.toLinearMap.comp JX.J = JY.J.comp A.deriv.toLinearMap :=
  A.phase_linear_deriv

/-- Pointwise Cauchy-Riemann law. -/
theorem HKColimit_cauchyRiemann_apply
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {JX : HestenesKreinSpace X} {JY : HestenesKreinSpace Y}
    {F : X → Y} {x : X}
    (A : HKColimit_HKAnalyticAt (inferInstance : HestenesKreinSpace X)
      (inferInstance : HestenesKreinSpace Y) F x)
    (v : X) :
    A.deriv (JX.J v) = JY.J (A.deriv v) :=
  LinearMap.congr_fun A.phase_linear_deriv v

/-- Construct `HKColimit_HKAnalyticAt` from a continuous linear map that is phase-linear. -/
def HKColimit_HKAnalyticAt.ofContinuousLinearMap
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {JX : HestenesKreinSpace X}
    {JY : HestenesKreinSpace Y}
    (L : X →L[ℝ] Y)
    (hL : L.toLinearMap.comp JX.J = JY.J.comp L.toLinearMap)
    (x : X) :
    HKColimit_HKAnalyticAt (inferInstance : HestenesKreinSpace X)
      (inferInstance : HestenesKreinSpace Y) (fun y : X => L y) x :=
  ⟨L, by simpa using L.hasFDerivAt, hL⟩

/-- The identity map is HK-analytic. -/
def HKAnalyticAt_id
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {JX : HestenesKreinSpace X}
    (x : X) :
    HKColimit_HKAnalyticAt (inferInstance : HestenesKreinSpace X)
      (inferInstance : HestenesKreinSpace X) (fun y : X => y) x :=
  HKColimit_HKAnalyticAt.id (inferInstance : HestenesKreinSpace X) x

end InfoGeometry.Analytic.HKColimit
