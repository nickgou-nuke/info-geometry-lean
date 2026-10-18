/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge

/-!
# Residue-readout calculation for the rank-two logarithmic object

This owner composes the square-zero cross-residue readout with tensor flip and
computes its double action exactly.  It records an operator calculation only;
it does not assert a braid or Yang--Baxter law.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanResidueCheckedRCalculation

open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.LogJordanTensorFusion
open InfoGeometry.Canonical.LogJordanTensorFusionDepth

def residueCheckedR (p : ℂ) :
    (standardJordanObject ⊗[ℂ] standardJordanObject) ≃ₗ[ℂ]
      (standardJordanObject ⊗[ℂ] standardJordanObject) :=
  (crossUnipotentEquiv standardJordanObject standardJordanObject_sq_zero p).trans
    (logCheckedR standardJordanObject standardJordanObject_sq_zero p)

@[simp]
theorem residueCheckedR_tmul (p : ℂ) (x y : standardJordanObject) :
    residueCheckedR p (x ⊗ₜ[ℂ] y) =
      y ⊗ₜ[ℂ] x + p • (standardJordanObject.N y ⊗ₜ[ℂ] standardJordanObject.N x) := by
  change logCheckedR standardJordanObject standardJordanObject_sq_zero p
    (crossUnipotentMap standardJordanObject standardJordanObject_sq_zero p
      (x ⊗ₜ[ℂ] y)) = _
  rw [crossUnipotentMap_tmul]
  simp only [map_add, logCheckedR_tmul, map_smul]

theorem residueCheckedR_double_tmul (p : ℂ) (x y : standardJordanObject) :
    (residueCheckedR p).trans (residueCheckedR p) (x ⊗ₜ[ℂ] y) =
      x ⊗ₜ[ℂ] y + (2 * p) •
        (standardJordanObject.N x ⊗ₜ[ℂ] standardJordanObject.N y) := by
  change residueCheckedR p (residueCheckedR p (x ⊗ₜ[ℂ] y)) = _
  calc
    _ = residueCheckedR p
        (y ⊗ₜ[ℂ] x + p • (standardJordanObject.N y ⊗ₜ[ℂ]
          standardJordanObject.N x)) := by rw [residueCheckedR_tmul]
    _ = residueCheckedR p (y ⊗ₜ[ℂ] x) +
        p • residueCheckedR p (standardJordanObject.N y ⊗ₜ[ℂ]
          standardJordanObject.N x) := by rw [map_add, map_smul]
    _ = (x ⊗ₜ[ℂ] y + p • (standardJordanObject.N x ⊗ₜ[ℂ]
          standardJordanObject.N y)) +
        p • (standardJordanObject.N x ⊗ₜ[ℂ] standardJordanObject.N y +
          p • (standardJordanObject.N (standardJordanObject.N x) ⊗ₜ[ℂ]
            standardJordanObject.N (standardJordanObject.N y))) := by
      rw [residueCheckedR_tmul, residueCheckedR_tmul]
    _ = x ⊗ₜ[ℂ] y + (2 * p) •
        (standardJordanObject.N x ⊗ₜ[ℂ] standardJordanObject.N y) := by
      rw [show standardJordanObject.N (standardJordanObject.N x) = 0 from
          N_apply_twice standardJordanObject standardJordanObject_sq_zero x,
        show standardJordanObject.N (standardJordanObject.N y) = 0 from
          N_apply_twice standardJordanObject standardJordanObject_sq_zero y]
      simp
      module

/-- A nonzero residue parameter gives nonidentity double action whenever the
cross-residue tensor detected by `x` and `y` is nonzero. -/
theorem residueCheckedR_double_ne_id_of (p : ℂ) (hp : p ≠ 0)
    (x y : standardJordanObject)
    (hxy : standardJordanObject.N x ⊗ₜ[ℂ] standardJordanObject.N y ≠ 0) :
    ((residueCheckedR p).trans (residueCheckedR p)).toLinearMap ≠
      LinearMap.id := by
  intro hid
  have heval := congrArg (fun f =>
      f (x ⊗ₜ[ℂ] y)) hid
  have hfixed : ((residueCheckedR p).trans (residueCheckedR p)).toLinearMap
      (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] y := by
    simpa only [LinearMap.id_apply] using heval
  have hformula := residueCheckedR_double_tmul p x y
  have hzero : (2 * p : ℂ) •
      (standardJordanObject.N x ⊗ₜ[ℂ] standardJordanObject.N y) = 0 := by
    have hcancel : x ⊗ₜ[ℂ] y + (2 * p : ℂ) •
        (standardJordanObject.N x ⊗ₜ[ℂ] standardJordanObject.N y) =
          x ⊗ₜ[ℂ] y := by
      calc
        _ = ((residueCheckedR p).trans (residueCheckedR p)).toLinearMap
            (x ⊗ₜ[ℂ] y) := hformula.symm
        _ = x ⊗ₜ[ℂ] y := hfixed
    exact add_left_cancel hcancel
  have hp2 : (2 * p : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hp
  rcases smul_eq_zero.mp hzero with hcoeff | htensor
  · exact hp2 hcoeff
  · exact hxy htensor

end InfoGeometry.Categorical.LogJordanResidueCheckedRCalculation
