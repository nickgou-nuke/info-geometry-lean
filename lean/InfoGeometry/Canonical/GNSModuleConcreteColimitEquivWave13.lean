/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FilteredGNSRepresentation
import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSModuleConcreteColimitEquiv

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
open CategoryTheory CategoryTheory.Limits

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

local notation "G" => GNSStage Stage sys ω
local notation "GS" => filteredGNSIsometricDirectSystem Stage sys ω
local notation "D∞" => AlgebraicGNSHilbertColimit Stage sys ω
local notation "M∞" => GNSModuleColimit Stage sys ω

/-- The concrete direct-limit stage maps form a `ModuleCat` cocone over the
native completed GNS diagram. -/
def concreteCocone : Cocone (gnsModuleDiagram Stage sys ω) where
  pt := ModuleCat.of ℂ D∞
  ι :=
    { app := fun i =>
        ModuleCat.ofHom (stageToDirectLimitLinearMap G GS i)
      naturality := by
        intro i j f
        ext x
        change
          stageToDirectLimitLinearMap G GS j
              ((gnsDirectInductiveSystem Stage sys ω).f
                (leOfHom f) x) =
            stageToDirectLimitLinearMap G GS i x
        change
          stageToDirectLimitLinearMap G GS j
              (filteredGNSMapCLM Stage sys ω (leOfHom f)
                (show G i from x)) = _
        rw [filteredGNSMapCLM_apply, ← filteredGNSLinearIsometry_apply]
        exact stageToDirectLimitLinearMap_transition G GS
            (leOfHom f) (show G i from x) }

/-- The comparison from Mathlib's native GNS `ModuleCat` colimit to the
concrete algebraic direct-limit carrier. -/
noncomputable def nativeToConcrete : M∞ →ₗ[ℂ] D∞ :=
  (colimit.desc (gnsModuleDiagram Stage sys ω)
    (concreteCocone Stage sys ω)).hom

@[simp] theorem nativeToConcrete_stage
    (i : I) (x : G i) :
    nativeToConcrete Stage sys ω
        (gnsColimitInclusion Stage sys ω i x) =
      stageToDirectLimitLinearMap G GS i x := by
  have h := colimit.ι_desc (concreteCocone Stage sys ω) i
  exact congrArg
    (fun f : (gnsModuleDiagram Stage sys ω).obj i ⟶
        (concreteCocone Stage sys ω).pt => f x) h

/-- Real-linear stage maps into the native `ModuleCat` colimit. -/
def nativeStageRealMap (i : I) :
    G i →ₗ[ℝ] M∞ where
  toFun := gnsColimitInclusion Stage sys ω i
  map_add' := (gnsColimitInclusion Stage sys ω i).map_add
  map_smul' := by
    intro r x
    exact (gnsColimitInclusion Stage sys ω i).map_smul r x

/-- The native colimit stage maps are compatible with the real direct-limit
bonding maps. -/
theorem nativeStageRealMap_compatible
    (i j : I) (hij : i ≤ j) (x : G i) :
    nativeStageRealMap Stage sys ω j
        (realTransition G GS hij x) =
      nativeStageRealMap Stage sys ω i x := by
  change
    gnsColimitInclusion Stage sys ω j
        (filteredGNSLinearIsometry Stage sys ω hij x) =
      gnsColimitInclusion Stage sys ω i x
  rw [filteredGNSLinearIsometry_apply]
  exact (gnsColimitInclusion_transition Stage sys ω hij x).symm

/-- Real-linear descent from the concrete direct-limit carrier to the native
`ModuleCat` colimit. -/
def concreteToNativeReal : D∞ →ₗ[ℝ] M∞ :=
  Module.DirectLimit.lift
    ℝ I G
    (fun _ _ hij => realTransition G GS hij)
    (nativeStageRealMap Stage sys ω)
    (nativeStageRealMap_compatible Stage sys ω)

@[simp] theorem concreteToNativeReal_stage
    (i : I) (x : G i) :
    concreteToNativeReal Stage sys ω
        (stageToDirectLimitLinearMap G GS i x) =
      gnsColimitInclusion Stage sys ω i x := by
  change
    concreteToNativeReal Stage sys ω
      (Module.DirectLimit.of ℝ I G
        (fun _ _ h => realTransition G GS h) i x) = _
  exact Module.DirectLimit.lift_of
    (g := nativeStageRealMap Stage sys ω)
    (nativeStageRealMap_compatible Stage sys ω) x

/-- Complex-linear descent obtained from the same real direct-limit descent. -/
def concreteToNative : D∞ →ₗ[ℂ] M∞ where
  toFun := concreteToNativeReal Stage sys ω
  map_add' := (concreteToNativeReal Stage sys ω).map_add
  map_smul' := by
    intro c z
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
        rw [complex_smul_of]
        change
          concreteToNativeReal Stage sys ω
              (stageToDirectLimitLinearMap G GS i (c • x)) =
            c • concreteToNativeReal Stage sys ω
              (stageToDirectLimitLinearMap G GS i x)
        simp only [concreteToNativeReal_stage]
        exact (gnsColimitInclusion Stage sys ω i).map_smul c x

@[simp] theorem concreteToNative_stage
    (i : I) (x : G i) :
    concreteToNative Stage sys ω
        (stageToDirectLimitLinearMap G GS i x) =
      gnsColimitInclusion Stage sys ω i x := by
  exact concreteToNativeReal_stage Stage sys ω i x

/-- The two comparison maps are inverse on the native categorical colimit. -/
theorem concreteToNative_comp_nativeToConcrete :
    (concreteToNative Stage sys ω).comp
      (nativeToConcrete Stage sys ω) = LinearMap.id := by
  have hcat :
      ModuleCat.ofHom ((concreteToNative Stage sys ω).comp
        (nativeToConcrete Stage sys ω)) =
        𝟙 (colimit (gnsModuleDiagram Stage sys ω)) := by
    apply colimit.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change concreteToNative Stage sys ω
        (nativeToConcrete Stage sys ω
          (gnsColimitInclusion Stage sys ω i (show G i from x))) =
      gnsColimitInclusion Stage sys ω i (show G i from x)
    rw [nativeToConcrete_stage, concreteToNative_stage]
  exact congrArg ModuleCat.Hom.hom hcat

/-- The two comparison maps are inverse on the concrete direct-limit carrier. -/
theorem nativeToConcrete_comp_concreteToNative :
    (nativeToConcrete Stage sys ω).comp
      (concreteToNative Stage sys ω) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      change nativeToConcrete Stage sys ω
        (concreteToNative Stage sys ω
          (stageToDirectLimitLinearMap G GS i x)) = _
      rw [concreteToNative_stage, nativeToConcrete_stage]
      rfl

/-- Canonical complex-linear equivalence between the native categorical GNS
colimit and the concrete algebraic direct-limit carrier. -/
def nativeConcreteEquiv : M∞ ≃ₗ[ℂ] D∞ where
  toFun := nativeToConcrete Stage sys ω
  invFun := concreteToNative Stage sys ω
  left_inv := by
    intro z
    have h := congrArg (fun T => T z)
      (concreteToNative_comp_nativeToConcrete Stage sys ω)
    exact h
  right_inv := by
    intro z
    have h := congrArg (fun T => T z)
      (nativeToConcrete_comp_concreteToNative Stage sys ω)
    exact h
  map_add' := (nativeToConcrete Stage sys ω).map_add
  map_smul' := (nativeToConcrete Stage sys ω).map_smul

@[simp] theorem nativeConcreteEquiv_apply_stage
    (i : I) (x : G i) :
    nativeConcreteEquiv Stage sys ω
        (gnsColimitInclusion Stage sys ω i x) =
      stageToDirectLimitLinearMap G GS i x := by
  exact nativeToConcrete_stage Stage sys ω i x

@[simp] theorem nativeConcreteEquiv_symm_apply_stage
    (i : I) (x : G i) :
    (nativeConcreteEquiv Stage sys ω).symm
        (stageToDirectLimitLinearMap G GS i x) =
      gnsColimitInclusion Stage sys ω i x := by
  exact concreteToNative_stage Stage sys ω i x

end CStarStateColimit.Native.FilteredGNSModuleConcreteColimitEquiv
