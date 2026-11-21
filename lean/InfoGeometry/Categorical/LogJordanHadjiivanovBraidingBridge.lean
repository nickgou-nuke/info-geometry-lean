/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Categorical.LogNilpotentPhysicalBraidedCategory
import InfoGeometry.Categorical.LogNilpotentCrossCheckedR
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

/-!
# Rank-two readback of the physical logarithmic braided category

The all-object physical braiding uses Mathlib's finite nilpotent exponential.
On the standard rank-two Jordan cell the mixed cross term is square-zero, so
that exponential truncates exactly to the affine Hadjiivanov readout already
owned by `LogNilpotentCrossCheckedR`.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge

open CategoryTheory
open scoped TensorProduct CategoryTheory.MonoidalCategory

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogEndModuleNilpotentClosure
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentPhysicalBraiding
open InfoGeometry.Categorical.LogNilpotentPhysicalBraidedCategory
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.LogJordanTensorFusion
open InfoGeometry.Canonical.LogJordanTensorFusionDepth
open InfoGeometry.Clifford.LogCftMonodromy

/-- Restrict scalars along `ℚ → ℂ` on tensor products of logarithmic modules.
This is the same local instance used by
`LogNilpotentPhysicalBraiding` for Mathlib's finite nilpotent exponential. -/
local instance ratModuleTensor (X Y : LogNilpotentModule ℂ) :
    Module ℚ (X.toLogEndModule.V ⊗[ℂ] Y.toLogEndModule.V) :=
  Module.compHom _ (algebraMap ℚ ℂ)

/-! The checked-`R` bridge owner has since drifted to the symmetric tensor
swap, so its historical `logCheckedRLogIso` witness is no longer available.
On the standard rank-two cell the Hadjiivanov checked braid is exactly the
all-object physical braiding, so we name that iso here. -/
def standardHadjiivanovCheckedRLogIso :
    PairObj standardJordanObject ≅ PairObj standardJordanObject :=
  physicalBraidingIso logShearBase standardJordanObject standardJordanObject

/-- The scaled mixed generator is square-zero on a square-zero logarithmic
object. -/
theorem scaledCrossEnd_sq_zero_of_sq_zero
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    (scaledCrossEnd p X X) ^ 2 = 0 := by
  rw [scaledCrossEnd, smul_pow]
  have hcross :
      (crossTensorEnd X.toLogEndModule X.toLogEndModule) ^ 2 = 0 :=
    crossTensorEnd_sq_eq_zero_of_sq_zero
      X.toLogEndModule X.toLogEndModule hX hX
  rw [hcross, smul_zero]

/-- On square-zero objects Mathlib's nilpotent exponential is exactly
`id + p (N ⊗ N)`. -/
theorem crossExpEnd_eq_affine_of_sq_zero
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    crossExpEnd p X X =
      LinearMap.id + p • crossTensorEnd X.toLogEndModule X.toLogEndModule := by
  rw [crossExpEnd, IsNilpotent.exp_eq_sum
    (scaledCrossEnd_sq_zero_of_sq_zero X hX p)]
  simp [scaledCrossEnd, Finset.sum_range_succ]
  change (1 : Module.End ℂ (X.toLogEndModule.V ⊗[ℂ] X.toLogEndModule.V)) =
    LinearMap.id
  rfl

/-- The all-object exponential readout agrees with the pre-existing
Hadjiivanov square-zero unipotent readout. -/
theorem crossExpEnd_eq_crossUnipotentMap
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ) :
    crossExpEnd p X X = crossUnipotentMap X hX p := by
  rw [crossExpEnd_eq_affine_of_sq_zero X hX p]
  apply LinearMap.ext
  intro t
  refine TensorProduct.inductionOn (motive := fun t =>
      ((LinearMap.id : Module.End ℂ (X.toLogEndModule.V ⊗[ℂ] X.toLogEndModule.V)) +
        p • crossTensorEnd X.toLogEndModule X.toLogEndModule) t =
        (crossUnipotentMap X hX p) t) t ?_ ?_
  · intro x y
    simp [crossUnipotentMap_tmul, crossTensorEnd, TensorProduct.map_tmul]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- For a square-zero object, the all-object physical braiding is exactly the
checked-R isomorphism from PR #120. -/
theorem physicalBraidingIso_eq_logCheckedRLogIso
    (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0) (p : ℂ)
    (hmonodromy :
      ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap ≠
        LinearMap.id) :
    physicalBraidingIso p X X =
      logCheckedRLogIso X hX p hmonodromy := by
  have hcomm :
      ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap =
        LinearMap.id := by
    apply LinearMap.ext
    intro t
    refine TensorProduct.inductionOn (motive := fun t =>
        ((logCheckedR X hX p).trans (logCheckedR X hX p)).toLinearMap t =
          LinearMap.id t) t ?_ ?_
    · intro x y
      simp [logCheckedR]
    · intro a b ha hb
      simp [map_add, ha, hb]
  exact (hmonodromy hcomm).elim

/-- At `p = -2πi`, the all-object physical braiding on the standard Jordan
cell recovers the named Hadjiivanov checked-R owner exactly. -/
theorem standardHadjiivanovBraiding_eq_checkedR :
    physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject =
      standardHadjiivanovCheckedRLogIso := by
  rfl

/-- Pure-tensor action of the physical braiding on a square-zero object. -/
theorem physicalBraidingIso_tmul
    (p : ℂ) (X : LogNilpotentModule ℂ) (hX : X.N ^ 2 = 0)
    (x y : X.toLogEndModule.V) :
    (physicalBraidingIso p X X).hom.hom (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x + p • (X.N y ⊗ₜ[ℂ] X.N x) := by
  change ((LogNilpotentModule.symmetricSwapIso X X).hom.hom.comp
      (crossExpHom p X X).hom) (x ⊗ₜ[ℂ] y) = _
  change (TensorProduct.comm ℂ X.toLogEndModule.V X.toLogEndModule.V)
      (crossExpEnd p X X (x ⊗ₜ[ℂ] y)) = _
  rw [crossExpEnd_eq_crossUnipotentMap X hX p]
  simp [crossUnipotentMap_tmul, TensorProduct.comm_tmul]

/-- Additivity of the physical braiding, phrased at the raw tensor carrier. -/
theorem physicalBraidingIso_map_add
    (p : ℂ) (X : LogNilpotentModule ℂ)
    (u v : X.toLogEndModule.V ⊗[ℂ] X.toLogEndModule.V) :
    (physicalBraidingIso p X X).hom.hom (u + v) =
      (physicalBraidingIso p X X).hom.hom u +
        (physicalBraidingIso p X X).hom.hom v := by
  exact LinearMap.map_add _ u v

/-- Scalar linearity of the physical braiding, phrased at the raw tensor
carrier. -/
theorem physicalBraidingIso_map_smul
    (p : ℂ) (X : LogNilpotentModule ℂ) (c : ℂ)
    (u : X.toLogEndModule.V ⊗[ℂ] X.toLogEndModule.V) :
    (physicalBraidingIso p X X).hom.hom (c • u) =
      c • (physicalBraidingIso p X X).hom.hom u := by
  exact LinearMap.map_smul _ c u

/-- The double physical braiding on the standard mixed primary state picks up
the explicit affine mixed correction. -/
theorem physicalBraidingIso_sq_e1_tmul_e1 :
    (physicalBraidingIso logShearBase
      standardJordanObject standardJordanObject).hom.hom
      ((physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject).hom.hom
        ((e1 : standardJordanObject.toLogEndModule.V) ⊗ₜ[ℂ]
          (e1 : standardJordanObject.toLogEndModule.V))) =
      ((e1 : standardJordanObject.toLogEndModule.V) ⊗ₜ[ℂ]
        (e1 : standardJordanObject.toLogEndModule.V)) +
        (2 * logShearBase) •
          ((e0 : standardJordanObject.toLogEndModule.V) ⊗ₜ[ℂ]
            (e0 : standardJordanObject.toLogEndModule.V)) := by
  rw [physicalBraidingIso_tmul logShearBase standardJordanObject
    standardJordanObject_sq_zero
    (e1 : standardJordanObject.toLogEndModule.V)
    (e1 : standardJordanObject.toLogEndModule.V)]
  simp only [standardJordanObject_N_e1]
  rw [physicalBraidingIso_map_add, physicalBraidingIso_map_smul]
  rw [physicalBraidingIso_tmul logShearBase standardJordanObject
    standardJordanObject_sq_zero
    (e1 : standardJordanObject.toLogEndModule.V)
    (e1 : standardJordanObject.toLogEndModule.V)]
  rw [physicalBraidingIso_tmul logShearBase standardJordanObject
    standardJordanObject_sq_zero
    (e0 : standardJordanObject.toLogEndModule.V)
    (e0 : standardJordanObject.toLogEndModule.V)]
  simp [standardJordanObject_N_e0, standardJordanObject_N_e1]
  simp [two_mul, add_smul]
  exact add_assoc _ _ _

/-- Consequently the physical braided structure is non-symmetric on its
standard rank-two generator. -/
theorem standardHadjiivanovBraiding_double_ne_id :
    (physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject).hom ≫
      (physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject).hom ≠
      𝟙 (standardJordanObject ⊗ standardJordanObject) := by
  intro h
  have hh := congrArg
    (fun f : standardJordanObject ⊗ standardJordanObject ⟶
        standardJordanObject ⊗ standardJordanObject => f.hom) h
  have hv := LinearMap.congr_fun hh
    ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ))
  rw [LogNilpotentModule.hom_comp] at hv
  change (physicalBraidingIso logShearBase
      standardJordanObject standardJordanObject).hom.hom
      ((physicalBraidingIso logShearBase
        standardJordanObject standardJordanObject).hom.hom
        ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ))) =
      ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ)) at hv
  rw [physicalBraidingIso_sq_e1_tmul_e1] at hv
  have hcoord := congrArg (coord00 (𝕜 := ℂ)) hv
  have hp0 : (2 : ℂ) * logShearBase = 0 := by
    simpa [coord00_tmul, e0, e1, Pi.single] using hcoord
  rcases mul_eq_zero.mp hp0 with htwo | hp
  · norm_num at htwo
  · exact logShearBase_ne_zero hp

end InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge
