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

end

end InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

