/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredDirectLimitOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Carrier.HestenesKrein
import InfoGeometry.Geometry.BilingualAnalyticity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex

open InfoGeometry.Carrier

/-!
# Filtered Inductive Colimit + Hestenes-Krein Analyticity - Core Structures

This file defines the core structures for Hestenes-Krein phase-linear real Fréchet
differentiability (`HKColimit_HKAnalyticAt`, `HKColimitOn`) and the single-carrier
compatible approximant structure (`FilteredInductiveHKAnalytic`).

## Scope & Ontology Note

- `HKColimit_HKAnalyticAt`: Genuine real Fréchet differentiability (`HasFDerivAt F deriv x`)
  whose derivative commutes with the fundamental symmetries (`deriv.toLinearMap.comp JX.J = JY.J.comp deriv.toLinearMap`).
- `FilteredInductiveHKAnalytic`: Single-carrier constant-sequence compatibility datum
  (`approx_compat : ∀ n m : ℕ, n ≤ m → approx n = approx m` and `limit_eq : F = approx 0`).
  Genuine multi-stage directed-system colimit phase transport over `AddCommGroup.DirectLimit`
  is owned by `InfoGeometry.Analytic.HKColimitAnalyticity.FilteredKreinPhaseFamily`.
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

/-- Canonical identity inhabitant of `HKColimit_HKAnalyticAt` at any point `x : X`. -/
def HKColimit_HKAnalyticAt.id
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (JX : HestenesKreinSpace X) (x : X) :
    HKColimit_HKAnalyticAt JX JX (fun y : X => y) x where
  deriv := ContinuousLinearMap.id ℝ X
  has_fderiv_at := (ContinuousLinearMap.id ℝ X).hasFDerivAt
  phase_linear_deriv := by
    ext v
    rfl

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

/-- Single-carrier compatible family of HK-analytic functions whose zeroth stage equals `F`. -/
structure FilteredInductiveHKAnalytic
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [HestenesKreinSpace X]
    (F : X → X) where
  /-- The stage approximants. -/
  approx : ℕ → (X → X)
  /-- Each approximant is HK-analytic. -/
  approx_hk : ∀ n : ℕ, ∀ x : X,
    HKColimit_HKAnalyticAt inferInstance inferInstance (approx n) x
  /-- The approximants form a constant compatible sequence. -/
  approx_compat : ∀ n m : ℕ, n ≤ m → approx n = approx m
  /-- The zeroth stage recovers `F`. -/
  limit_eq : F = approx 0

/-- Canonical identity inhabitant of `FilteredInductiveHKAnalytic`. -/
def FilteredInductiveHKAnalytic.id
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [HestenesKreinSpace X] :
    FilteredInductiveHKAnalytic (fun y : X => y) where
  approx := fun _ y => y
  approx_hk := fun _ x => HKColimit_HKAnalyticAt.id inferInstance x
  approx_compat := fun _ _ _ => rfl
  limit_eq := rfl

/-- Concrete 1D real `HestenesKreinSpace ℝ` model with `krein_form x y = x * y` and `J = id`. -/
noncomputable instance realHestenesKreinSpace : HestenesKreinSpace ℝ where
  krein_form := LinearMap.mul ℝ ℝ
  J := LinearMap.id
  J_involution := rfl
  induced_hilbert_identity v hv := by
    change 0 < v * v
    exact mul_self_pos.mpr hv

/-- Concrete ground-type inhabitant of `HKColimit_HKAnalyticAt` on `ℝ` at `0`. -/
noncomputable def realIdHKAnalyticAtZero :
    HKColimit_HKAnalyticAt realHestenesKreinSpace realHestenesKreinSpace (fun y : ℝ => y) 0 :=
  HKColimit_HKAnalyticAt.id realHestenesKreinSpace 0

/-- Concrete ground-type inhabitant of `FilteredInductiveHKAnalytic` on `ℝ`. -/
noncomputable def realIdFilteredInductiveHKAnalytic :
    FilteredInductiveHKAnalytic (fun y : ℝ => y) :=
  FilteredInductiveHKAnalytic.id
