import InfoGeometry.Canonical.RestrictedVolumeCharacter
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.BogoliubovClosedForms
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Weyl Gauge Operator Lift

Operator-first Weyl/volume transport on the doubled real Krein carrier.

This file keeps the owner objects on the lifted operator side:
- sheetwise lifted automorphisms on `DoubledSpace E`,
- their decomposition into common Weyl gauge and relative `ε`-dilation parts,
- the generalized determinant character as an external group homomorphism,
- and the multiplicative/additive chain rules for transported phase-space volume.

The determinant is used only as a character attached to lifted transport data.
It is not promoted to a scalar replacement for the operator surface.
-/

namespace InfoGeometry.Canonical.WeylGaugeOperatorLift

open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Volume.Base
open InfoGeometry.Volume.DeterminantBundle

section Lifted

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Sheetwise lifted automorphism data on the doubled carrier. -/
structure LiftedSheetAut where
  plus : E ≃L[ℝ] E
  minus : E ≃L[ℝ] E

namespace LiftedSheetAut

/-- Forget to the split determinant-character surface. -/
def toRestrictedSheetEquiv (g : LiftedSheetAut (E := E)) : RestrictedSheetEquiv E where
  plus := g.plus.toLinearEquiv
  minus := g.minus.toLinearEquiv

/-- Operator lift of the sheetwise transport to the doubled carrier. -/
noncomputable def liftedOperator (g : LiftedSheetAut (E := E)) : EndH :=
  dualSheetPairLift (E := E) g.plus.toContinuousLinearMap g.minus.toContinuousLinearMap

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem plusBlockMap_liftedOperator (g : LiftedSheetAut (E := E)) :
    plusBlockMap (E := E) (liftedOperator g) = g.plus.toContinuousLinearMap := by
  simp [liftedOperator]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem minusBlockMap_liftedOperator (g : LiftedSheetAut (E := E)) :
    minusBlockMap (E := E) (liftedOperator g) = g.minus.toContinuousLinearMap := by
  simp [liftedOperator]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem plusToMinusBlockMap_liftedOperator (g : LiftedSheetAut (E := E)) :
    plusToMinusBlockMap (E := E) (liftedOperator g) = 0 := by
  simp [liftedOperator]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem minusToPlusBlockMap_liftedOperator (g : LiftedSheetAut (E := E)) :
    minusToPlusBlockMap (E := E) (liftedOperator g) = 0 := by
  simp [liftedOperator]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem plusProjectorFlux_liftedOperator (g : LiftedSheetAut (E := E)) :
    plusProjectorFlux (E := E) (liftedOperator g) = 0 := by
  simp [liftedOperator]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem minusProjectorFlux_liftedOperator (g : LiftedSheetAut (E := E)) :
    minusProjectorFlux (E := E) (liftedOperator g) = 0 := by
  simp [liftedOperator]

/-- Sequential composition of sheetwise lifted transports. -/
def mulTransport (g h : LiftedSheetAut (E := E)) : LiftedSheetAut (E := E) where
  plus := h.plus.trans g.plus
  minus := h.minus.trans g.minus

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem liftedOperator_mulTransport (g h : LiftedSheetAut (E := E)) :
    liftedOperator (mulTransport g h) = (liftedOperator g).comp (liftedOperator h) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext <;>
    simp [liftedOperator, mulTransport, dualSheetPairLift_apply_to_doubled, ContinuousLinearMap.comp_apply]

/-- Generalized determinant character attached to the lifted transport. -/
noncomputable def determinantCharacter (g : LiftedSheetAut (E := E)) : ℝˣ :=
  RestrictedSheetEquiv.restrictedVolumeCharacter (E := E) (toRestrictedSheetEquiv g)

/-- Positive relative phase-space volume scale carried by the lifted transport. -/
noncomputable def relativeVolumeScale (g : LiftedSheetAut (E := E)) : ℝ :=
  RestrictedSheetEquiv.restrictedVolumeScale (E := E) (toRestrictedSheetEquiv g)

/-- Additive logarithmic coordinate on the positive relative volume scale. -/
noncomputable def logRelativeVolumePotential (g : LiftedSheetAut (E := E)) : ℝ :=
  Real.log (relativeVolumeScale g)

/-- Split logarithmic Weyl coordinates attached to the lifted transport. -/
noncomputable def logPlusVolume (g : LiftedSheetAut (E := E)) : ℝ :=
  Real.log (volumeScale g.plus.toLinearEquiv)

noncomputable def logMinusVolume (g : LiftedSheetAut (E := E)) : ℝ :=
  Real.log (volumeScale g.minus.toLinearEquiv)

/-- Common Weyl-gauge logarithmic coordinate. -/
noncomputable def commonLogCoordinate (g : LiftedSheetAut (E := E)) : ℝ :=
  (logPlusVolume g + logMinusVolume g) / 2

/-- Relative/chiral logarithmic coordinate. -/
noncomputable def relativeLogCoordinate (g : LiftedSheetAut (E := E)) : ℝ :=
  (logPlusVolume g - logMinusVolume g) / 2

/-- Operator-valued logarithmic Weyl generator on the doubled carrier. -/
noncomputable def logarithmicGenerator (g : LiftedSheetAut (E := E)) : EndH :=
  commonLogCoordinate g • (ContinuousLinearMap.id ℝ H₂)
    + relativeLogCoordinate g • modularSignEpsilon (E := E)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem relativeVolumeScale_eq_abs_character (g : LiftedSheetAut (E := E)) :
    relativeVolumeScale g = |((determinantCharacter g : ℝˣ) : ℝ)| := by
  unfold relativeVolumeScale determinantCharacter
  simpa using RestrictedSheetEquiv.restrictedVolumeScale_eq_abs_character
    (E := E) (toRestrictedSheetEquiv g)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem determinantCharacter_gaugeRescale
    (w : E ≃L[ℝ] E) (g : LiftedSheetAut (E := E)) :
    determinantCharacter { plus := w.trans g.plus, minus := w.trans g.minus } = determinantCharacter g := by
  cases g
  unfold determinantCharacter toRestrictedSheetEquiv RestrictedSheetEquiv.restrictedVolumeCharacter VolumeHom
  simp [LinearEquiv.det_trans]
  group

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem relativeVolumeScale_gaugeRescale
    (w : E ≃L[ℝ] E) (g : LiftedSheetAut (E := E)) :
    relativeVolumeScale { plus := w.trans g.plus, minus := w.trans g.minus } = relativeVolumeScale g := by
  rw [relativeVolumeScale_eq_abs_character, relativeVolumeScale_eq_abs_character,
    determinantCharacter_gaugeRescale]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem determinantCharacter_mulTransport (g h : LiftedSheetAut (E := E)) :
    determinantCharacter (mulTransport g h) = determinantCharacter g * determinantCharacter h := by
  cases g
  cases h
  unfold determinantCharacter mulTransport toRestrictedSheetEquiv RestrictedSheetEquiv.restrictedVolumeCharacter VolumeHom
  simp [LinearEquiv.det_trans, mul_assoc, mul_left_comm, mul_comm]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem relativeVolumeScale_pos (g : LiftedSheetAut (E := E)) :
    0 < relativeVolumeScale g := by
  unfold relativeVolumeScale toRestrictedSheetEquiv RestrictedSheetEquiv.restrictedVolumeScale
    RestrictedSheetEquiv.plusSheetVolumeScale RestrictedSheetEquiv.minusSheetVolumeScale
  exact div_pos
    (RestrictedSheetEquiv.volumeScale_pos (f := g.plus.toLinearEquiv))
    (RestrictedSheetEquiv.volumeScale_pos (f := g.minus.toLinearEquiv))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem relativeVolumeScale_mulTransport (g h : LiftedSheetAut (E := E)) :
    relativeVolumeScale (mulTransport g h) = relativeVolumeScale g * relativeVolumeScale h := by
  rw [relativeVolumeScale_eq_abs_character, relativeVolumeScale_eq_abs_character,
    relativeVolumeScale_eq_abs_character, determinantCharacter_mulTransport]
  simp [abs_mul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem logRelativeVolumePotential_mulTransport (g h : LiftedSheetAut (E := E)) :
    logRelativeVolumePotential (mulTransport g h)
      = logRelativeVolumePotential g + logRelativeVolumePotential h := by
  unfold logRelativeVolumePotential
  rw [relativeVolumeScale_mulTransport]
  exact Real.log_mul (ne_of_gt (relativeVolumeScale_pos g)) (ne_of_gt (relativeVolumeScale_pos h))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem logRelativeVolumePotential_eq_logPlus_minus_logMinus
    (g : LiftedSheetAut (E := E)) :
    logRelativeVolumePotential g = logPlusVolume g - logMinusVolume g := by
  unfold logRelativeVolumePotential relativeVolumeScale toRestrictedSheetEquiv logPlusVolume logMinusVolume
    RestrictedSheetEquiv.restrictedVolumeScale RestrictedSheetEquiv.plusSheetVolumeScale
    RestrictedSheetEquiv.minusSheetVolumeScale
  simpa using Real.log_div
    (ne_of_gt (RestrictedSheetEquiv.volumeScale_pos (f := g.plus.toLinearEquiv)))
    (ne_of_gt (RestrictedSheetEquiv.volumeScale_pos (f := g.minus.toLinearEquiv)))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem logRelativeVolumePotential_eq_two_mul_relativeLogCoordinate
    (g : LiftedSheetAut (E := E)) :
    logRelativeVolumePotential g = (2 : ℝ) * relativeLogCoordinate g := by
  rw [logRelativeVolumePotential_eq_logPlus_minus_logMinus]
  unfold relativeLogCoordinate
  ring

/-- Gauge-balanced lifted transports act equally on both sheets. -/
def IsGaugeBalanced (g : LiftedSheetAut (E := E)) : Prop :=
  g.plus = g.minus

/-- Relative-volume-preserving lifted transports lie in the determinant-character kernel. -/
def IsRelativeVolumePreserving (g : LiftedSheetAut (E := E)) : Prop :=
  determinantCharacter g = 1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem determinantCharacter_eq_one_of_isGaugeBalanced
    {g : LiftedSheetAut (E := E)}
    (hBal : IsGaugeBalanced g) :
    determinantCharacter g = 1 := by
  cases g with
  | mk plus minus =>
      dsimp [IsGaugeBalanced] at hBal
      subst minus
      unfold determinantCharacter toRestrictedSheetEquiv RestrictedSheetEquiv.restrictedVolumeCharacter VolumeHom
      simp

/-- Reference transport from the isotropic vacuum/reference sheet by split logarithmic scales. -/
noncomputable def referenceTransport (a b : ℝ) : LiftedSheetAut (E := E) where
  plus := (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) (Real.exp a) (by positivity)).toContinuousLinearEquiv
  minus := (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) (Real.exp b) (by positivity)).toContinuousLinearEquiv

/-- Common-mode Weyl gauge transport from the reference state. -/
noncomputable def isotropicGaugeTransport (s : ℝ) : LiftedSheetAut (E := E) :=
  referenceTransport s s

/-- Relative `ε`-dilation transport from the reference state. -/
noncomputable def relativeDilationTransport (t : ℝ) : LiftedSheetAut (E := E) :=
  referenceTransport t (-t)

omit [CompleteSpace E] in
@[simp] theorem liftedOperator_referenceTransport (a b : ℝ) :
    liftedOperator (referenceTransport a b)
      = dualSheetDiagonalScalarOp (E := E) (Real.exp a) (Real.exp b) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext <;>
    simp [liftedOperator, referenceTransport, dualSheetDiagonalScalarOp,
      dualSheetPairLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      ContinuousLinearMap.comp_apply, LinearEquiv.smulOfNeZero_apply]

omit [CompleteSpace E] in
@[simp] theorem liftedOperator_isotropicGaugeTransport (s : ℝ) :
    liftedOperator (isotropicGaugeTransport s)
      = Real.exp s • (ContinuousLinearMap.id ℝ H₂) := by
  rw [show isotropicGaugeTransport (E := E) s = referenceTransport s s by rfl]
  rw [liftedOperator_referenceTransport]
  simpa using dualSheetDiagonalScalarOp_same (E := E) (rho := Real.exp s)

@[simp] theorem liftedOperator_relativeDilationTransport (t : ℝ) :
    liftedOperator (relativeDilationTransport t)
      = epsilonBoost (E := E) t := by
  rw [show relativeDilationTransport (E := E) t = referenceTransport t (-t) by rfl]
  rw [liftedOperator_referenceTransport]
  simpa using dualSheetDiagonalScalarOp_exp_pair_eq_epsilonBoost (E := E) t

theorem liftedOperator_referenceTransport_eq_gauge_smul_epsilonBoost
    (a b : ℝ) :
    liftedOperator (referenceTransport a b)
      = Real.exp ((a + b) / 2) • epsilonBoost (E := E) ((a - b) / 2) := by
  rw [liftedOperator_referenceTransport]
  let c : ℝ := (a + b) / 2
  let t : ℝ := (a - b) / 2
  have ha : Real.exp a = Real.exp c * Real.exp t := by
    dsimp [c, t]
    rw [← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp b = Real.exp c * Real.exp (-t) := by
    dsimp [c, t]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ha, hb]
  rw [dualSheetDiagonalScalarOp_weylGaugeRescale (E := E) (sigma := Real.exp c)
    (rhoPlus := Real.exp t) (rhoMinus := Real.exp (-t))]
  rw [dualSheetDiagonalScalarOp_exp_pair_eq_epsilonBoost]

/-- The common Weyl-gauge family commutes with the relative `ε`-dilation family. -/
theorem isotropicGaugeTransport_commutes_relativeDilationTransport
    (s t : ℝ) :
    (liftedOperator (E := E) (isotropicGaugeTransport (E := E) s)).comp
        (liftedOperator (E := E) (relativeDilationTransport (E := E) t))
      =
      (liftedOperator (E := E) (relativeDilationTransport (E := E) t)).comp
        (liftedOperator (E := E) (isotropicGaugeTransport (E := E) s)) := by
  rw [liftedOperator_isotropicGaugeTransport (E := E),
    liftedOperator_relativeDilationTransport (E := E)]
  calc
    (Real.exp s • ContinuousLinearMap.id ℝ H₂).comp (epsilonBoost (E := E) t)
      = Real.exp s • epsilonBoost (E := E) t := by simp
    _ = (epsilonBoost (E := E) t).comp (Real.exp s • ContinuousLinearMap.id ℝ H₂) := by simp

end LiftedSheetAut
end Lifted

end InfoGeometry.Canonical.WeylGaugeOperatorLift
