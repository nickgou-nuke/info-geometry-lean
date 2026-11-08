/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl44VolumeElement
import InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-!
# Native `Cl(4,4)` volume action on the four-mode left ideal

The existing owner proves set-level closure of the ideal `Cl44 * f` under
left multiplication. This module packages left multiplication by the native
ordered volume element as a real-linear endomorphism of that range submodule
and proves that the endomorphism is an involution. It does not identify this
ideal with the separate matrix Fock carrier or assert its dimension.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.Cl44NativeVolumeIdealAction

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl44VolumeElement
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis

/-- Left multiplication by the native `Cl(4,4)` volume element on the
four-mode vacuum-generated left ideal `Cl44 * f`. -/
def volumeLeftAction :
    cl44LeftIdealSubmodule →ₗ[ℝ] cl44LeftIdealSubmodule where
  toFun x := ⟨volumeElement * x.1, by
    rcases LinearMap.mem_range.mp x.2 with ⟨y, hy⟩
    simp only [LinearMap.mulRight_apply] at hy
    refine LinearMap.mem_range.mpr ⟨volumeElement * y, ?_⟩
    calc
      (volumeElement * y) * cl44VacuumIdempotent =
          volumeElement * (y * cl44VacuumIdempotent) := by rw [mul_assoc]
      _ = volumeElement * x.1 := by rw [hy]
  ⟩
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' c x := by
    apply Subtype.ext
    calc
      volumeElement * (algebraMap ℝ Cl44 c * x.1) =
          (volumeElement * algebraMap ℝ Cl44 c) * x.1 := by rw [mul_assoc]
      _ = (algebraMap ℝ Cl44 c * volumeElement) * x.1 := by
        rw [(Algebra.commutes c volumeElement).symm]
      _ = algebraMap ℝ Cl44 c * (volumeElement * x.1) := by rw [mul_assoc]

/-- The volume-element action is an involution on the native ideal. -/
theorem volumeLeftAction_involutive (x : cl44LeftIdealSubmodule) :
    volumeLeftAction (volumeLeftAction x) = x := by
  apply Subtype.ext
  change volumeElement * (volumeElement * x.1) = x.1
  rw [← mul_assoc, volumeElement_sq]
  simp

end InfoGeometry.Synthesis.Cl44NativeVolumeIdealAction

end
