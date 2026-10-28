/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PluckerCl55InfinityBridge
import InfoGeometry.Clifford.Cl55RealSplitPinAction

/-!
# The native sheet reflection on the Lorentzian Klein slice

The actual complex linear twistor involution `(ω,π) ↦ (-iπ,iω)` induces a
signed exterior-square action. It intertwines the Lorentzian six-coordinate
slice with the existing native Clifford reflection and its split Pin lift.
On the graph chart its action is `X ↦ -X⁻¹`, with homogeneous scale `-det X`.
The endpoint signs record the owner's opposite Klein/native quadratic forms.
-/

noncomputable section

namespace InfoGeometry.Twistor.PluckerSheetReflection

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorPlucker
open InfoGeometry.Twistor.InfinityTwistor
open InfoGeometry.Twistor.PluckerInfinityChart
open InfoGeometry.Twistor.PluckerBlockInversion
open InfoGeometry.Twistor.PluckerLorentzRealForm
open InfoGeometry.Twistor.PluckerCl55InfinityBridge
open InfoGeometry.Bridge.ZornConformalSixCone
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open InfoGeometry.Clifford.Clifford55

section Ring

variable {R : Type*} [CommRing R]

/-- Exterior-square action of the phase-corrected spinor block exchange. -/
def signedSheetPlucker (P : Plucker6 R) : Plucker6 R :=
  ⟨-P.p23, -P.p02, -P.p12, -P.p03, -P.p13, -P.p01⟩

@[simp] theorem signedSheetPlucker_involutive (P : Plucker6 R) :
    signedSheetPlucker (signedSheetPlucker P) = P := by
  cases P
  simp [signedSheetPlucker]

theorem signedSheetPlucker_scale (c : R) (P : Plucker6 R) :
    signedSheetPlucker (Plucker6.scale c P) =
      Plucker6.scale c (signedSheetPlucker P) := by
  apply Plucker6.ext <;> simp [signedSheetPlucker, Plucker6.scale]

@[simp] theorem signedSheetPlucker_p23 (P : Plucker6 R) :
    (signedSheetPlucker P).p23 = -P.p01 := rfl

@[simp] theorem kleinQ_signedSheetPlucker (P : Plucker6 R) :
    kleinQ (signedSheetPlucker P) = kleinQ P := by
  simp [kleinQ, signedSheetPlucker]
  ring

theorem kleinPolar_signedSheetPlucker (P Q : Plucker6 R) :
    kleinPolar (signedSheetPlucker P) (signedSheetPlucker Q) = kleinPolar P Q := by
  simp [kleinPolar, signedSheetPlucker]
  ring

theorem signedSheetPlucker_origin :
    signedSheetPlucker (graphPlucker (0 : Matrix (Fin 2) (Fin 2) R)) =
      Plucker6.scale (-1) infinityPlucker := by
  apply Plucker6.ext <;>
    simp [signedSheetPlucker, graphPlucker_coordinates,
      infinityPlucker_coordinates, Plucker6.scale]

theorem signedSheetPlucker_infinity :
    signedSheetPlucker (infinityPlucker (R := R)) =
      Plucker6.scale (-1) (graphPlucker (0 : Matrix (Fin 2) (Fin 2) R)) := by
  apply Plucker6.ext <;>
    simp [signedSheetPlucker, graphPlucker_coordinates,
      infinityPlucker_coordinates, Plucker6.scale]

end Ring

/-- The graph action is negative inverse; the native incidence map has its
separate factor `i`, as recorded in `PluckerPenroseIncidence`. -/
theorem signedSheetPlucker_graphPlucker {R : Type*} [Field R]
    (X : Matrix (Fin 2) (Fin 2) R) (hX : X.det ≠ 0) :
    signedSheetPlucker (graphPlucker X) =
      Plucker6.scale (-X.det) (graphPlucker (-X⁻¹)) := by
  apply Plucker6.ext
  · simp [signedSheetPlucker, graphPlucker_coordinates, Plucker6.scale,
      Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hX]
  all_goals
    simp [signedSheetPlucker, graphPlucker_coordinates, Plucker6.scale,
      Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two] <;>
      field_simp [hX]

/-- Actual linear involution on the native twistor carrier. -/
def twistorSheetReflection : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (-Complex.I • Z.2, Complex.I • Z.1)
  invFun Z := (-Complex.I • Z.2, Complex.I • Z.1)
  left_inv Z := by rcases Z with ⟨ω, π⟩; simp [smul_smul]
  right_inv Z := by rcases Z with ⟨ω, π⟩; simp [smul_smul]
  map_add' Z W := by simp [smul_add]
  map_smul' c Z := by simp [smul_smul, mul_comm]

@[simp] theorem twistorSheetReflection_apply (Z : Twistor4) :
    twistorSheetReflection Z = (-Complex.I • Z.2, Complex.I • Z.1) := rfl

@[simp] theorem twistorSheetReflection_involutive (Z : Twistor4) :
    twistorSheetReflection (twistorSheetReflection Z) = Z := by
  simp [smul_smul]

/-- The six-coordinate action is the actual exterior square of the twistor map. -/
theorem twistorPairPlucker_sheetReflection (Z W : Twistor4) :
    twistorPairPlucker (twistorSheetReflection Z) (twistorSheetReflection W) =
      signedSheetPlucker (twistorPairPlucker Z W) := by
  apply Plucker6.ext <;> apply Complex.ext <;>
    simp [twistorPairPlucker, twistorProjectiveVector, pluckerLine,
      signedSheetPlucker, smul_eq_mul] <;> ring

theorem infinityTwistor_sheetReflection (Z W : Twistor4) :
    infinityTwistor (twistorSheetReflection Z) (twistorSheetReflection W) =
      -(twistorPairPlucker Z W).p01 := by
  rw [infinityTwistor_eq_plucker_p23, twistorPairPlucker_sheetReflection]
  rfl

/-- Reflection of the four negative directions in the real `(2,4)` slice. -/
def sheetReflectionSix (X : ConformalSix) : ConformalSix :=
  ⟨X.a0, -X.ax, -X.ay, -X.az, -X.b0, X.bz⟩

@[simp] theorem sheetReflectionSix_involutive (X : ConformalSix) :
    sheetReflectionSix (sheetReflectionSix X) = X := by
  cases X
  simp [sheetReflectionSix]

@[simp] theorem quadratic24_sheetReflectionSix (X : ConformalSix) :
    quadratic24 (sheetReflectionSix X) = quadratic24 X := by
  simp [quadratic24, sheetReflectionSix]

theorem lorentzPlucker_sheetReflectionSix (X : ConformalSix) :
    lorentzPlucker (sheetReflectionSix X) = signedSheetPlucker (lorentzPlucker X) := by
  apply Plucker6.ext <;> apply Complex.ext <;>
    simp [lorentzPlucker, sheetReflectionSix, signedSheetPlucker] <;> ring

theorem lorentzConjugation_signedSheetPlucker (P : Plucker6 ℂ) :
    lorentzConjugation (signedSheetPlucker P) =
      signedSheetPlucker (lorentzConjugation P) := by
  apply Plucker6.ext <;> simp [lorentzConjugation, signedSheetPlucker]

/-- An actual representing pair is carried to a pair on the reflected real slice. -/
theorem twistorPairPlucker_sheetReflection_real (Z W : Twistor4) (X : ConformalSix)
    (hX : twistorPairPlucker Z W = lorentzPlucker X) :
    twistorPairPlucker (twistorSheetReflection Z) (twistorSheetReflection W) =
      lorentzPlucker (sheetReflectionSix X) := by
  rw [twistorPairPlucker_sheetReflection, hX, lorentzPlucker_sheetReflectionSix]

/-- The six-dimensional slice is preserved by the owner's ten-dimensional action. -/
theorem conformalSixToV55_sheetReflectionSix (X : ConformalSix) :
    conformalSixToV55 (sheetReflectionSix X) =
      globalSheetReflection (conformalSixToV55 X) := by
  ext i <;> fin_cases i <;>
    simp [conformalSixToV55, conformalSixToPAC55, pacSplit55ToV55,
      sheetReflectionSix, globalSheetReflection]

theorem nativeClifford_sheetReflection (X : ConformalSix) :
    globalSheetReflectionAlg (ι55 (conformalSixToV55 X)) =
      ι55 (conformalSixToV55 (sheetReflectionSix X)) := by
  rw [globalSheetReflectionAlg_apply_ι, conformalSixToV55_sheetReflectionSix]

/-- Compatibility with the already constructed split Pin element, not an
identification with an unspecified element of a different Pin presentation. -/
theorem realSplitPin_sheetReflection (X : ConformalSix) :
    realSplitPinTwistedAction globalSheetRealSplitPin (conformalSixToV55 X) =
      conformalSixToV55 (sheetReflectionSix X) := by
  rw [realSplitPinTwistedAction_globalSheet_eq_globalSheetReflection]
  change globalSheetReflection (conformalSixToV55 X) = _
  exact (conformalSixToV55_sheetReflectionSix X).symm

end InfoGeometry.Twistor.PluckerSheetReflection
