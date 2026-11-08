/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

/-!
# Concrete chirality projectors on the native Hestenes image

This module keeps the chiral splitting on the actual image carrier.  It does
not identify that image with the full 32-dimensional master carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeConcreteChiralityProjectorBridge

open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit

abbrev Image := nativeConcreteHestenesImage

local notation "EndImage" => Module.End ℝ Image

/-- The `+1` projector of the concrete image chirality involution. -/
noncomputable def nativeConcreteChiralityProjectorPlus : EndImage :=
  ((2 : ℝ)⁻¹) • ((1 : EndImage) + nativeConcreteChiralityOnImage)

/-- The `-1` projector of the concrete image chirality involution. -/
noncomputable def nativeConcreteChiralityProjectorMinus : EndImage :=
  ((2 : ℝ)⁻¹) • ((1 : EndImage) - nativeConcreteChiralityOnImage)

/-- The positive concrete chirality projector is idempotent. -/
theorem nativeConcreteChiralityProjectorPlus_idempotent :
    nativeConcreteChiralityProjectorPlus.comp
        nativeConcreteChiralityProjectorPlus =
      nativeConcreteChiralityProjectorPlus := by
  apply LinearMap.ext
  intro z
  simp only [nativeConcreteChiralityProjectorPlus, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.map_add, LinearMap.map_smul]
  have hsq : nativeConcreteChiralityOnImage
        (nativeConcreteChiralityOnImage z) = z := by
    have h := congrArg (fun F : EndImage => F z)
      nativeConcreteChiralityOnImage_sq
    simpa [LinearMap.comp_apply] using h
  rw [hsq]
  module

/-- The negative concrete chirality projector is idempotent. -/
theorem nativeConcreteChiralityProjectorMinus_idempotent :
    nativeConcreteChiralityProjectorMinus.comp
        nativeConcreteChiralityProjectorMinus =
      nativeConcreteChiralityProjectorMinus := by
  apply LinearMap.ext
  intro z
  simp only [nativeConcreteChiralityProjectorMinus, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.map_sub, LinearMap.map_smul]
  have hsq : nativeConcreteChiralityOnImage
        (nativeConcreteChiralityOnImage z) = z := by
    have h := congrArg (fun F : EndImage => F z)
      nativeConcreteChiralityOnImage_sq
    simpa [LinearMap.comp_apply] using h
  rw [hsq]
  module

/-- The two concrete chirality projectors are mutually orthogonal. -/
theorem nativeConcreteChiralityProjectors_orthogonal :
    nativeConcreteChiralityProjectorPlus.comp
        nativeConcreteChiralityProjectorMinus = 0 ∧
      nativeConcreteChiralityProjectorMinus.comp
        nativeConcreteChiralityProjectorPlus = 0 := by
  constructor <;>
    apply LinearMap.ext <;> intro z
  · simp only [nativeConcreteChiralityProjectorPlus,
      nativeConcreteChiralityProjectorMinus, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.map_sub,
      LinearMap.map_smul, LinearMap.zero_apply]
    have hsq : nativeConcreteChiralityOnImage
          (nativeConcreteChiralityOnImage z) = z := by
      have h := congrArg (fun F : EndImage => F z)
        nativeConcreteChiralityOnImage_sq
      simpa [LinearMap.comp_apply] using h
    rw [hsq]
    module
  · simp only [nativeConcreteChiralityProjectorPlus,
      nativeConcreteChiralityProjectorMinus, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.map_add,
      LinearMap.map_smul, LinearMap.zero_apply]
    have hsq : nativeConcreteChiralityOnImage
          (nativeConcreteChiralityOnImage z) = z := by
      have h := congrArg (fun F : EndImage => F z)
        nativeConcreteChiralityOnImage_sq
      simpa [LinearMap.comp_apply] using h
    rw [hsq]
    module

/-- The two concrete chirality projectors resolve the identity on the image. -/
theorem nativeConcreteChiralityProjectors_sum :
    nativeConcreteChiralityProjectorPlus +
        nativeConcreteChiralityProjectorMinus =
      (1 : EndImage) := by
  apply LinearMap.ext
  intro z
  simp only [nativeConcreteChiralityProjectorPlus,
    nativeConcreteChiralityProjectorMinus, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.one_apply]
  module

/-- The positive projector transports the `+1` concrete chirality sector. -/
theorem nativeConcreteChiralityProjectorPlus_intertwines_embeddingEquiv
    (x : DoubledExterior3) :
    nativeConcreteChiralityProjectorPlus
        (nativeConcreteHestenesEmbeddingEquiv x) =
      ((2 : ℝ)⁻¹) •
        nativeConcreteHestenesEmbeddingEquiv
          (x + concreteChirality3 x) := by
  simp only [nativeConcreteChiralityProjectorPlus, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.one_apply,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv]
  rw [map_add]

/-- The negative projector transports the `-1` concrete chirality sector. -/
theorem nativeConcreteChiralityProjectorMinus_intertwines_embeddingEquiv
    (x : DoubledExterior3) :
    nativeConcreteChiralityProjectorMinus
        (nativeConcreteHestenesEmbeddingEquiv x) =
      ((2 : ℝ)⁻¹) •
        nativeConcreteHestenesEmbeddingEquiv
          (x - concreteChirality3 x) := by
  simp only [nativeConcreteChiralityProjectorMinus, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply,
    nativeConcreteChiralityOnImage_intertwines_embeddingEquiv]
  rw [map_sub]

end InfoGeometry.Canonical.RealCl55NativeConcreteChiralityProjectorBridge
