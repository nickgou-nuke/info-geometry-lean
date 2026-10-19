/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge
import InfoGeometry.Canonical.RealCl55NativeConcreteChiralityProjectorBridge

/-!
# Phase-flow transport of concrete chirality

The native phase flow and the concrete chirality involution commute on the
actual Hestenes image.  The two chiral projectors therefore commute with the
flow as well.  This is an operator identity on the native image, with no
identification with the larger master carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowChiralityBridge

open InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowBridge
open InfoGeometry.Canonical.RealCl55NativeConcreteChiralityProjectorBridge
open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

local notation "EndImage" => Module.End ℝ nativeConcreteHestenesImage

theorem nativeConcretePhaseFlowOnImage_comp_chirality (t : ℝ) :
    (nativeConcretePhaseFlowOnImage t).comp
        nativeConcreteChiralityOnImage =
      nativeConcreteChiralityOnImage.comp
        (nativeConcretePhaseFlowOnImage t) := by
  apply LinearMap.ext
  intro z
  rw [← nativeConcreteHestenesEmbeddingEquiv.apply_symm_apply z]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv,
    nativeConcretePhaseFlowOnImage_intertwines_embeddingEquiv,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv]
  apply Subtype.ext
  rw [concreteHestenesPhaseFlow_eq_linear_combination t]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, Module.End.one_apply]
  have hχ := congrArg (fun T : DoubledExterior3End =>
      T (nativeConcreteHestenesEmbeddingEquiv.symm z))
    concreteHestenesPhase_chirality_commutes
  simp only [Module.End.mul_apply] at hχ
  rw [hχ]

theorem nativeConcretePhaseFlowOnImage_comp_chiralityProjectorPlus
    (t : ℝ) :
    (nativeConcretePhaseFlowOnImage t).comp
        nativeConcreteChiralityProjectorPlus =
      nativeConcreteChiralityProjectorPlus.comp
        (nativeConcretePhaseFlowOnImage t) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, nativeConcreteChiralityProjectorPlus,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.map_add, LinearMap.map_smul]
  have hχ := congrArg (fun F : EndImage => F z)
    (nativeConcretePhaseFlowOnImage_comp_chirality t)
  simp only [LinearMap.comp_apply] at hχ
  rw [hχ]

theorem nativeConcretePhaseFlowOnImage_comp_chiralityProjectorMinus
    (t : ℝ) :
    (nativeConcretePhaseFlowOnImage t).comp
        nativeConcreteChiralityProjectorMinus =
      nativeConcreteChiralityProjectorMinus.comp
        (nativeConcretePhaseFlowOnImage t) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, nativeConcreteChiralityProjectorMinus,
    LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.map_sub, LinearMap.map_smul]
  have hχ := congrArg (fun F : EndImage => F z)
    (nativeConcretePhaseFlowOnImage_comp_chirality t)
  simp only [LinearMap.comp_apply] at hχ
  rw [hχ]

end InfoGeometry.Canonical.RealCl55NativeConcretePhaseFlowChiralityBridge
