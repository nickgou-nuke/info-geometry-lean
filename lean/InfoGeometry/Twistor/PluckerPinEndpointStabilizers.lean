/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerSheetReflection
import InfoGeometry.Canonical.Cl55WittPinConformalBoundaryBridge
import InfoGeometry.Clifford.Cl55WittPinParity

/-!
# The signed sheet reflection exchanges the native endpoint stabilizers

The boundary owner uses ordinary Pin conjugation. Its action on the odd
five-reflection element is minus the twisted sheet reflection, a sign that
disappears projectively but must be retained on vectors. Conjugation by this
actual native Pin element exchanges the stabilizers of the unnormalized
infinity and origin vectors. The same action preserves the embedded real
six-dimensional carrier, with its homogeneous sign recorded explicitly.
-/

noncomputable section

namespace InfoGeometry.Twistor.PluckerPinEndpointStabilizers

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Bridge.ZornConformalSixCone
open InfoGeometry.Twistor.PluckerCl55InfinityBridge
open InfoGeometry.Twistor.PluckerSheetReflection
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open InfoGeometry.Canonical.Cl55WittPinConformalBoundaryBridge

theorem globalSheetPin_involute :
    CliffordAlgebra.involute (pinToUnits globalSheetPin : Cl55) =
      -(pinToUnits globalSheetPin : Cl55) := by
  rw [pinToUnits_globalSheetPin, globalSheetUnit_coe, globalSheetPin_coe]
  simp only [map_mul, CliffordAlgebra.involute_ι]
  noncomm_ring

/-- Ordinary and twisted Pin actions have opposite signs on this odd element. -/
theorem pinNative_globalSheet_apply (v : V55) :
    pinNativeOrthogonalAction globalSheetPin v = -globalSheetReflection v := by
  have h := congrArg (fun f : V55 →ₗ[ℝ] V55 => f v)
    (pinTwistedAction_eq_neg_pinConjAction_of_involute_eq_neg
      globalSheetPin globalSheetPin_involute)
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection] at h
  change globalSheetReflection v = -pinNativeOrthogonalAction globalSheetPin v at h
  simpa only [neg_neg] using congrArg (fun w : V55 => -w) h.symm

theorem pinNative_globalSheet_infinity :
    pinNativeOrthogonalAction globalSheetPin nativeInfinityVector = -n_vec := by
  rw [pinNative_globalSheet_apply]
  ext i <;> fin_cases i <;>
    simp [nativeInfinityVector, pacSplit55ToV55, pacSplit55Infinity,
      globalSheetReflection, n_vec, n_pair, e_pos, f_neg]

theorem pinNative_globalSheet_origin :
    pinNativeOrthogonalAction globalSheetPin n_vec = -nativeInfinityVector := by
  rw [pinNative_globalSheet_apply]
  ext i <;> fin_cases i <;>
    simp [nativeInfinityVector, pacSplit55ToV55, pacSplit55Infinity,
      globalSheetReflection, n_vec, n_pair, e_pos, f_neg]

theorem pinNative_globalSheet_inv_origin :
    pinNativeOrthogonalAction globalSheetPin⁻¹ n_vec = -nativeInfinityVector := by
  apply (pinNativeOrthogonalAction globalSheetPin).injective
  change pinNativeOrthogonalAction globalSheetPin
      (pinNativeOrthogonalAction globalSheetPin⁻¹ n_vec) =
    pinNativeOrthogonalAction globalSheetPin (-nativeInfinityVector)
  rw [← pinNativeOrthogonalAction_mul_apply, mul_inv_cancel]
  rw [map_neg, pinNative_globalSheet_infinity, neg_neg]
  rw [pinNativeOrthogonalAction_apply_vector, pinConjAction_one]
  rfl

/-- A genuine conjugation criterion for the existing infinity stabilizer. -/
theorem globalSheetPin_conjugate_origin_iff (g : Pin55) :
    pinNativeOrthogonalAction (globalSheetPin * g * globalSheetPin⁻¹) n_vec = n_vec ↔
      g ∈ pinInfinityStabilizer := by
  change pinNativeOrthogonalAction (globalSheetPin * g * globalSheetPin⁻¹) n_vec = n_vec ↔
    pinNativeOrthogonalAction g nativeInfinityVector = nativeInfinityVector
  rw [pinNativeOrthogonalAction_mul_apply, pinNativeOrthogonalAction_mul_apply,
    pinNative_globalSheet_inv_origin, map_neg, map_neg]
  constructor
  · intro h
    apply (pinNativeOrthogonalAction globalSheetPin).injective
    change pinNativeOrthogonalAction globalSheetPin
        (pinNativeOrthogonalAction g nativeInfinityVector) =
      pinNativeOrthogonalAction globalSheetPin nativeInfinityVector
    rw [pinNative_globalSheet_infinity]
    simpa only [neg_neg] using congrArg (fun w : V55 => -w) h
  · intro h
    rw [h, pinNative_globalSheet_infinity, neg_neg]

theorem pinNative_globalSheet_conformalSix (X : ConformalSix) :
    pinNativeOrthogonalAction globalSheetPin (conformalSixToV55 X) =
      conformalSixToV55
        (InfoGeometry.Bridge.ZornConformalSixCone.scale (-1) (sheetReflectionSix X)) := by
  rw [pinNative_globalSheet_apply, conformalSixToV55_scale,
    conformalSixToV55_sheetReflectionSix]
  simp

theorem pinNative_globalSheet_preserves_conformalSix
    (v : V55) (hv : v ∈ Set.range conformalSixToV55) :
    pinNativeOrthogonalAction globalSheetPin v ∈ Set.range conformalSixToV55 := by
  rcases hv with ⟨X, rfl⟩
  exact ⟨InfoGeometry.Bridge.ZornConformalSixCone.scale (-1) (sheetReflectionSix X),
    (pinNative_globalSheet_conformalSix X).symm⟩

end InfoGeometry.Twistor.PluckerPinEndpointStabilizers
