/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Native filtered and inverse readouts for the `Cl(1,1)` tower

This owner packages the existing finite matrix tower in the repository's
`ModuleCat` filtered-colimit interface.  The normalized trace is recorded as
the corresponding compatible inverse family of dual linear maps.  No analytic
completion, infinite tensor product, or second colimit carrier is introduced.

## Audit Classification
- **BUCKET 1 (Genuine Constructive Proofs)**:
  - `directSystem`, `colimitCocone`, `colimitCocone_eval`
  - `traceCocone`, `traceCocone_eval`, `nativeModuleColimit`
  - `limitReadout`, `limitReadout_stage`, `limitReadout_stage_apply`
  - `traceReadout`, `traceReadout_stage`, `traceReadout_stage_apply`
  - `dualTraceTransition`, `dualTraceTransition_apply`, `normalizedTrace_dual_compatibility`,
    `bondMap_smul`
- **BUCKET 2 (Honest Numeric/Finite Certificates)**: None.
- **BUCKET 3 (Eliminated Debt)**: `0` `sorry`, `0` `admit`, `0` wrapper structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge

open CategoryTheory CategoryTheory.Limits
open FilteredColimit
open FilteredColimit.Native
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
open InfoGeometry.Canonical.Cl11TensorInductiveLimit

abbrev Stage (n : ℕ) : Type := MatStage n
abbrev Limit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- Direct inductive system of the `Cl(1,1)` finite matrix stages over `ℝ`. -/
def directSystem : DirectInductiveSystem ℝ ℕ Stage :=
  DirectInductiveSystem.mk
    (fun {m n} h => (stageEmbedMap h).toLinearMap)
    (by
      intro n
      apply LinearMap.ext
      intro x
      exact stageEmbedMap_apply_refl n x)
    (by
      intro m n k hmn hnk
      apply LinearMap.ext
      intro x
      change stageEmbedMap hnk (stageEmbedMap hmn x) =
        stageEmbedMap (hmn.trans hnk) x
      exact congrArg (fun F => F x) (stageEmbedMap_comp hmn hnk))

/-- Inductive cocone from the finite `Cl(1,1)` stages into `Limit`. -/
def colimitCocone : InductiveCocone ℝ directSystem Limit :=
  ⟨fun n => (ofStageAlgHom n).toLinearMap, by
    intro m n h
    ext x
    change ofStage n (stageEmbedMap h x) = ofStage m x
    induction h with
    | refl =>
        simp [stageEmbedMap_refl]
    | @step n h ih =>
        rw [stageEmbedMap_succ h]
        change ofStage (n + 1)
            (stageEmbed n (stageEmbedMap h x)) = ofStage m x
        rw [ofStage_apply_bond]
        exact ih⟩

/-- Stage evaluation compatibility for `colimitCocone`. -/
theorem colimitCocone_eval
    {m n : ℕ} (h : m ≤ n) (x : Stage m) :
    colimitCocone.psi n (directSystem.f h x) =
      colimitCocone.psi m x := by
  have hc := InductiveCocone.cocone_eval_comm colimitCocone h x
  exact hc

/-- Inductive cocone induced by the normalized matrix trace `normalizedTraceLinear n`. -/
def traceCocone : InductiveCocone ℝ directSystem ℝ :=
  ⟨fun n =>
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n, by
    intro m n h
    ext x
    change normalizedTrace n (stageEmbedMap h x) = normalizedTrace m x
    exact normalizedTrace_stageEmbedMap h x⟩

/-- Stage evaluation compatibility for `traceCocone`. -/
theorem traceCocone_eval
    {m n : ℕ} (h : m ≤ n) (x : Stage m) :
    traceCocone.psi n (directSystem.f h x) =
      traceCocone.psi m x := by
  have hc := InductiveCocone.cocone_eval_comm traceCocone h x
  exact hc

/-- Native `ModuleCat ℝ` colimit of the `Cl(1,1)` direct inductive system. -/
noncomputable def nativeModuleColimit : ModuleCat ℝ :=
  colimit (moduleDiagram directSystem)

/-- Universal linear morphism from `nativeModuleColimit` into `Limit`. -/
noncomputable def limitReadout :
    nativeModuleColimit ⟶ ModuleCat.of ℝ Limit :=
  descendModuleCocone directSystem colimitCocone

/-- Stage factorization of `limitReadout` along `colimit.ι`. -/
@[reassoc]
theorem limitReadout_stage (n : ℕ) :
    colimit.ι (moduleDiagram directSystem) n ≫ limitReadout =
      (moduleCocone directSystem colimitCocone).ι.app n := by
  have h := moduleColimit_desc_stage directSystem colimitCocone n
  exact h

/-- Pointwise evaluation of `limitReadout` on an element `x : Stage n` embedded via `colimit.ι`. -/
theorem limitReadout_stage_apply (n : ℕ) (x : Stage n) :
    limitReadout ((colimit.ι (moduleDiagram directSystem) n).hom x) =
      ofStage n x := by
  have h := congrArg (fun f => f x) (limitReadout_stage n)
  exact h

/-- Universal trace readout from `nativeModuleColimit` into `ℝ`. -/
noncomputable def traceReadout :
    nativeModuleColimit ⟶ ModuleCat.of ℝ ℝ :=
  descendModuleCocone directSystem traceCocone

/-- Stage factorization of `traceReadout` along `colimit.ι`. -/
@[reassoc]
theorem traceReadout_stage (n : ℕ) :
    colimit.ι (moduleDiagram directSystem) n ≫ traceReadout =
      (moduleCocone directSystem traceCocone).ι.app n := by
  have h := moduleColimit_desc_stage directSystem traceCocone n
  exact h

/-- Pointwise evaluation of `traceReadout` on an element `x : Stage n` embedded via `colimit.ι`. -/
theorem traceReadout_stage_apply (n : ℕ) (x : Stage n) :
    traceReadout ((colimit.ι (moduleDiagram directSystem) n).hom x) =
      normalizedTrace n x := by
  have h := congrArg (fun f => f x) (traceReadout_stage n)
  exact h

/-- Contravariant dual transition map `(Stage n →ₗ[ℝ] ℝ) →ₗ[ℝ] (Stage m →ₗ[ℝ] ℝ)` for `m ≤ n`. -/
def dualTraceTransition {m n : ℕ} (h : m ≤ n) :
    (Stage n →ₗ[ℝ] ℝ) →ₗ[ℝ] (Stage m →ₗ[ℝ] ℝ) :=
  FilteredColimit.InductiveCocone.dualInverseTransition directSystem h

/-- Pointwise evaluation of `dualTraceTransition` by precomposition with `directSystem.f h`. -/
theorem dualTraceTransition_apply
    {m n : ℕ} (h : m ≤ n) (φ : Stage n →ₗ[ℝ] ℝ) (x : Stage m) :
    dualTraceTransition h φ x = φ (directSystem.f h x) := by
  change (φ.comp (directSystem.f h)) x = φ (directSystem.f h x)
  rfl

/-- Compatibility of `normalizedTraceLinear` with `dualTraceTransition`. -/
theorem normalizedTrace_dual_compatibility
    {m n : ℕ} (h : m ≤ n) (x : Stage m) :
    dualTraceTransition h
        (InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear n) x =
      InfoGeometry.Clifford.Cl11MarkovJonesEngine.normalizedTraceLinear m x := by
  have ht := normalizedTrace_stageEmbedMap h x
  exact ht

/-- `bondMap stageBond m n h` commutes with real scalar multiplication. -/
theorem bondMap_smul
    {m n : ℕ} (h : m ≤ n) (c : ℝ) (x : Stage m) :
    bondMap stageBond m n h (c • x) =
      c • bondMap stageBond m n h x := by
  induction n, h using Nat.le_induction with
  | base =>
      simp [bondMap_refl]
  | succ n h ih =>
      rw [bondMap_succ]
      change stageBond n (bondMap stageBond m n h (c • x)) =
        c • stageBond n (bondMap stageBond m n h x)
      rw [ih]
      change stageEmbed n (c • bondMap stageBond m n h x) =
        c • stageEmbed n (bondMap stageBond m n h x)
      simp only [Algebra.smul_def, map_mul, (stageEmbed n).commutes]

end InfoGeometry.Canonical.Cl11FilteredInductiveInverseColimitBridge
