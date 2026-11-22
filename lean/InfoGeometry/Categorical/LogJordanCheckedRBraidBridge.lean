/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.LogNilpotentCrossCheckedR
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LogJordanTensorFusionDepth
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

Concrete logarithmic checked braid on the repository's standard rank-two
Jordan cell.

The generic tensor-symmetry lane is the Mathlib tensor swap.  The coefficient
`logShearBase` is retained as source data, but no non-symmetric shear datum is
constructed here until its Yang--Baxter and monodromy laws are proved.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.LogJordanTensorFusion
open InfoGeometry.Canonical.LogJordanTensorFusionDepth
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.QuantumG2RMatrixBraidingDatum
open InfoGeometry.Clifford.LogCftMonodromy

/-- The standard square-zero rank-two logarithmic object. -/
def standardJordanObject : LogNilpotentModule ℂ where
  toLogEndModule :=
    { V := JordanCarrier ℂ
      N := jordanNilpotentLinear }
  nilpotencyOrder := 2
  nilpotent := by
    simpa [pow_two, Module.End.mul_eq_comp] using
      (jordanNilpotentLinear_sq_zero (𝕜 := ℂ))

/-- Square-zero certificate in the exact form consumed by the checked-`R`
construction. -/
theorem standardJordanObject_sq_zero :
    standardJordanObject.N ^ 2 = 0 := by
  exact standardJordanObject.nilpotent

@[simp]
theorem standardJordanObject_N_e0 :
    standardJordanObject.N (e0 : JordanCarrier ℂ) = 0 := by
  exact jordanNilpotentLinear_e0 (𝕜 := ℂ)

@[simp]
theorem standardJordanObject_N_e1 :
    standardJordanObject.N (e1 : JordanCarrier ℂ) =
      (e0 : JordanCarrier ℂ) := by
  exact jordanNilpotentLinear_e1 (𝕜 := ℂ)

@[simp]
theorem standard_logCheckedR_e1_tmul_e1 (p : ℂ) :
    logCheckedR standardJordanObject standardJordanObject_sq_zero p
        ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ)) =
      (e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ) := by
  exact logCheckedR_tmul standardJordanObject standardJordanObject_sq_zero p
    (e1 : JordanCarrier ℂ) (e1 : JordanCarrier ℂ)

theorem standard_logCheckedR_monodromy_eq_id
    (p : ℂ) :
    ((logCheckedR standardJordanObject standardJordanObject_sq_zero p).trans
      (logCheckedR standardJordanObject standardJordanObject_sq_zero p)).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro t
  refine TensorProduct.inductionOn t ?_ ?_
  · intro x y
    simp [LinearEquiv.trans_apply, logCheckedR_tmul]
  · intro a b ha hb
    simpa only [map_add] using congrArg₂ (fun u v => u + v) ha hb

/-- The universal Hadjiivanov logarithmic shear coefficient is nonzero. -/
theorem logShearBase_ne_zero : logShearBase ≠ 0 := by
  unfold logShearBase
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by norm_num))
    Complex.I_ne_zero) hpi

theorem standard_logCheckedR_yangBaxter :
    (logCheckedR12 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR23 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR12 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap =
      (logCheckedR23 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR12 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR23 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap := by
  exact logCheckedR_yangBaxter standardJordanObject standardJordanObject_sq_zero logShearBase

/-! The categorical symmetric lane is defined directly from the existing
Mathlib tensor braiding; it does not pass through the checked-`R` datum
interface, whose additional monodromy field is intentionally non-symmetric. -/

def standardSymmetricSigmaOne :
    TripleObj standardJordanObject ⟶ TripleObj standardJordanObject :=
  (LogNilpotentModule.associatorIso standardJordanObject standardJordanObject
      standardJordanObject).inv ≫
    (LogNilpotentModule.tensorHom
      ((LogNilpotentModule.symmetricSwapIso standardJordanObject standardJordanObject).hom)
      (𝟙 standardJordanObject)) ≫
    (LogNilpotentModule.associatorIso standardJordanObject standardJordanObject
      standardJordanObject).hom

def standardSymmetricSigmaTwo :
  TripleObj standardJordanObject ⟶ TripleObj standardJordanObject :=
  LogNilpotentModule.tensorHom (𝟙 standardJordanObject)
    ((LogNilpotentModule.symmetricSwapIso standardJordanObject standardJordanObject).hom)

noncomputable section

/-- The general nontrivial checked logarithmic braid: a finite unipotent shear
followed by the tensor flip. -/
def shearCheckedR {X : LogNilpotentModule ℂ} (hX : X.N ^ 2 = 0) (p : ℂ) :
    (X.toLogEndModule.V ⊗[ℂ] X.toLogEndModule.V) ≃ₗ[ℂ]
      (X.toLogEndModule.V ⊗[ℂ] X.toLogEndModule.V) :=
  (crossUnipotentEquiv X hX p).trans
    (TensorProduct.comm ℂ X.toLogEndModule.V X.toLogEndModule.V)

@[simp]
theorem shearCheckedR_tmul {X : LogNilpotentModule ℂ} (hX : X.N ^ 2 = 0)
    (p : ℂ) (x y : X.toLogEndModule.V) :
    shearCheckedR hX p (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x + p • (X.N y ⊗ₜ[ℂ] X.N x) := by
  simp [shearCheckedR, crossUnipotentEquiv, LinearEquiv.trans_apply,
    crossUnipotentMap_tmul, TensorProduct.comm_tmul]

/-- Two applications of the sheared checked logarithmic braid differ from the
identity by the explicit mixed primary tensor state `(2 * p) • (e0 ⊗ₜ e0)`. -/
theorem standard_shearCheckedR_sq_e1_tmul_e1 (p : ℂ) :
    let R := shearCheckedR standardJordanObject_sq_zero p
    let v1 : standardJordanObject.toLogEndModule.V := (e1 : JordanCarrier ℂ)
    let v0 : standardJordanObject.toLogEndModule.V := (e0 : JordanCarrier ℂ)
    R (R (v1 ⊗ₜ[ℂ] v1)) = v1 ⊗ₜ[ℂ] v1 + (2 * p) • (v0 ⊗ₜ[ℂ] v0) := by
  intro R v1 v0
  have hN1 : standardJordanObject.N v1 = v0 := standardJordanObject_N_e1
  have hN0 : standardJordanObject.N v0 = 0 := standardJordanObject_N_e0
  have h1 : R (v1 ⊗ₜ[ℂ] v1) = v1 ⊗ₜ[ℂ] v1 + p • (v0 ⊗ₜ[ℂ] v0) := by
    simp [R, hN1]
  have h0 : R (v0 ⊗ₜ[ℂ] v0) = v0 ⊗ₜ[ℂ] v0 := by
    simp [R, hN0]
  rw [h1, map_add, map_smul, h1, h0]
  module

/-- Every nonzero logarithmic shear coefficient produces strictly nontrivial
double braiding on the standard rank-two Jordan cell. -/
theorem standard_shearCheckedR_monodromy_nontrivial
    (p : ℂ) (hp : p ≠ 0) :
    ((shearCheckedR standardJordanObject_sq_zero p).trans
      (shearCheckedR standardJordanObject_sq_zero p)).toLinearMap ≠
      LinearMap.id := by
  intro hmono
  let v1 : standardJordanObject.toLogEndModule.V := (e1 : JordanCarrier ℂ)
  let v0 : standardJordanObject.toLogEndModule.V := (e0 : JordanCarrier ℂ)
  have hv := LinearMap.congr_fun hmono (v1 ⊗ₜ[ℂ] v1)
  have hsq := standard_shearCheckedR_sq_e1_tmul_e1 p
  change
    shearCheckedR standardJordanObject_sq_zero p
        (shearCheckedR standardJordanObject_sq_zero p (v1 ⊗ₜ[ℂ] v1)) =
      v1 ⊗ₜ[ℂ] v1 at hv
  rw [hsq] at hv
  have hcoord : coord00 (𝕜 := ℂ)
      ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ) +
        (2 * p) • ((e0 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e0 : JordanCarrier ℂ))) =
      coord00 (𝕜 := ℂ) ((e1 : JordanCarrier ℂ) ⊗ₜ[ℂ] (e1 : JordanCarrier ℂ)) :=
    congrArg (coord00 (𝕜 := ℂ)) hv
  rw [map_add, map_smul] at hcoord
  have h2p : (2 : ℂ) * p = 0 := by
    simpa [coord00_tmul, e0, e1, Pi.single] using hcoord
  rcases mul_eq_zero.mp h2p with h2 | hp0
  · norm_num at h2
  · exact hp hp0

/-- The Hadjiivanov sheared checked braid at `logShearBase` has strictly
nontrivial double braiding. -/
theorem standardHadjiivanov_shear_monodromy_ne_id :
    ((shearCheckedR standardJordanObject_sq_zero logShearBase).trans
      (shearCheckedR standardJordanObject_sq_zero logShearBase)).toLinearMap ≠
      LinearMap.id :=
  standard_shearCheckedR_monodromy_nontrivial logShearBase logShearBase_ne_zero

/-- PR-named alias for the proved nontrivial Hadjiivanov monodromy. -/
theorem standardHadjiivanov_monodromy_ne_id :
    ((shearCheckedR standardJordanObject_sq_zero logShearBase).trans
      (shearCheckedR standardJordanObject_sq_zero logShearBase)).toLinearMap ≠
      LinearMap.id :=
  standardHadjiivanov_shear_monodromy_ne_id

/-- PR-named alias for the Yang--Baxter relation of the symmetric checked
braid at the Hadjiivanov parameter. -/
theorem standardHadjiivanov_yangBaxter :
    (logCheckedR12 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR23 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR12 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap =
      (logCheckedR23 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR12 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap ∘ₗ
          (logCheckedR23 standardJordanObject standardJordanObject_sq_zero logShearBase).toLinearMap :=
  standard_logCheckedR_yangBaxter

end

end InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

