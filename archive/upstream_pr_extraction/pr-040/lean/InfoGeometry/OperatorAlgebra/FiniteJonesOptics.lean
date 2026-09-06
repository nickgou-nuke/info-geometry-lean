/-
InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean

Finite-dimensional Jones optics instantiation.

This file gives the first concrete laboratory-ready instantiation of the
operator-Erlangen optical layer.

It works with diagonal 2 x 2 Jones matrices in either the `s/p` basis or the
circular `L/R` basis.

It proves concrete facts:

* Brewster reflection is a rank-collapse event.
* Total internal reflection / waveplate-style transport is lossless when both
  channel magnitudes are one.
* Metal mirrors may be modeled as lossy complex retarders/diattenuators.
* Chiral media may be modeled in the circular basis.

This file does not derive the coefficients from a material model. That belongs
to `SusceptibilityHessian.lean`.
-/

import Mathlib.Tactic
import InfoGeometry.Optics.JonesCalibration

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteJonesOptics

open InfoGeometry.Optics.JonesCalibration

/-! ## 1. Basic diagonal Jones events -/

/--
A coherent diagonal Jones event in a chosen polarization basis.

The two coefficients are interpreted according to the basis:

* `s/p` basis: `a = r_s`, `b = r_p`;
* circular basis: `a = r_L`, `b = r_R`.
-/
def diagonalEvent
    (basis : PolarizationBasis)
    (kind : OpticalSurfaceKind)
    (a b : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    JonesOpticalEvent where
  basis := basis
  kind := kind
  coeff0 := a
  coeff1 := b
  tag := tag

/-- A diagonal event in the `s/p` Fresnel basis. -/
def diagonalSPEvent
    (kind : OpticalSurfaceKind)
    (rs rp : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    JonesOpticalEvent :=
  diagonalEvent PolarizationBasis.sp kind rs rp tag

/-- A diagonal event in the circular `L/R` basis. -/
def diagonalCircularEvent
    (kind : OpticalSurfaceKind)
    (rL rR : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    JonesOpticalEvent :=
  diagonalEvent PolarizationBasis.circular kind rL rR tag

namespace diagonalEvent

@[simp]
theorem basis
    (basis : PolarizationBasis)
    (kind : OpticalSurfaceKind)
    (a b : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    (diagonalEvent basis kind a b tag).basis = basis :=
  rfl

@[simp]
theorem coeff0
    (basis : PolarizationBasis)
    (kind : OpticalSurfaceKind)
    (a b : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    (diagonalEvent basis kind a b tag).coeff0 = a :=
  rfl

@[simp]
theorem coeff1
    (basis : PolarizationBasis)
    (kind : OpticalSurfaceKind)
    (a b : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    (diagonalEvent basis kind a b tag).coeff1 = b :=
  rfl

end diagonalEvent

/-! ## 2. Concrete determinant for diagonal 2 x 2 Jones matrices -/

/--
Concrete determinant for a `2 x 2` Jones matrix.

This is intentionally local. It is enough to prove rank-collapse facts for
Brewster-style diagonal events.
-/
def det2 (M : JonesMat) : ℂ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/--
The determinant of a diagonal Jones matrix is the product of its channel
coefficients.
-/
theorem det2_diagJones
    (a b : ℂ) :
    det2 (diagJones a b) = a * b := by
  simp [det2, diagJones]

/--
The determinant of a calibrated diagonal event is the product of its two
coefficients.
-/
theorem det2_diagonalEvent_jones
    (basis : PolarizationBasis)
    (kind : OpticalSurfaceKind)
    (a b : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    det2 (diagonalEvent basis kind a b tag).jones = a * b := by
  unfold diagonalEvent JonesOpticalEvent.jones
  exact det2_diagJones a b

/-! ## 3. Brewster rank-collapse event -/

/--
A Brewster-rank-collapse event in the `s/p` basis.

The `p` channel vanishes while the `s` channel is nonzero.
-/
def brewsterEvent
    (rs : ℂ)
    (_hrs : rs ≠ 0) :
    JonesOpticalEvent :=
  diagonalSPEvent OpticalSurfaceKind.brewsterProjection rs 0 InfoGeometry.Geometry.KleinFourTag.P

/-- The Brewster event satisfies the abstract `IsBrewsterEvent` predicate. -/
theorem brewsterEvent_isBrewster
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    IsBrewsterEvent (brewsterEvent rs hrs) := by
  unfold IsBrewsterEvent brewsterEvent diagonalSPEvent diagonalEvent
  simp [hrs]

/-- At Brewster calibration, the second channel is zero. -/
theorem brewsterEvent_secondCoeff_zero
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    (brewsterEvent rs hrs).secondCoeff = 0 :=
  JonesOpticalEvent.brewster_secondCoeff_zero
    (brewsterEvent rs hrs)
    (brewsterEvent_isBrewster rs hrs)

/-- At Brewster calibration, the first channel is nonzero. -/
theorem brewsterEvent_firstCoeff_ne_zero
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    (brewsterEvent rs hrs).firstCoeff ≠ 0 :=
  JonesOpticalEvent.brewster_firstCoeff_ne_zero
    (brewsterEvent rs hrs)
    (brewsterEvent_isBrewster rs hrs)

/-- Brewster reflection is a rank-collapse event: its Jones determinant vanishes. -/
theorem det2_brewsterEvent_jones
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    det2 (brewsterEvent rs hrs).jones = 0 := by
  unfold brewsterEvent diagonalSPEvent diagonalEvent JonesOpticalEvent.jones
  rw [det2_diagJones]
  ring

/-! ## 4. Total internal reflection / lossless retarder event -/

/--
A lossless diagonal retarder in the `s/p` basis.

This can model idealized total internal reflection, waveplate-style transport,
or any lossless diagonal phase-retarder in the local polarization eigenbasis.
-/
def losslessSPRetarderEvent
    (rs rp : ℂ)
    (_hrs : ‖rs‖ = 1)
    (_hrp : ‖rp‖ = 1) :
    JonesOpticalEvent :=
  diagonalSPEvent OpticalSurfaceKind.totalInternalReflection rs rp InfoGeometry.Geometry.KleinFourTag.id

/-- The lossless retarder satisfies the abstract `IsLosslessRetarder` predicate. -/
theorem losslessSPRetarderEvent_isLossless
    (rs rp : ℂ)
    (hrs : ‖rs‖ = 1)
    (hrp : ‖rp‖ = 1) :
    IsLosslessRetarder (losslessSPRetarderEvent rs rp hrs hrp) := by
  unfold IsLosslessRetarder losslessSPRetarderEvent diagonalSPEvent diagonalEvent
  exact ⟨hrs, hrp⟩

/--
The determinant of a diagonal lossless retarder is the product of its two
phase coefficients.
-/
theorem det2_losslessSPRetarderEvent_jones
    (rs rp : ℂ)
    (hrs : ‖rs‖ = 1)
    (hrp : ‖rp‖ = 1) :
    det2 (losslessSPRetarderEvent rs rp hrs hrp).jones = rs * rp := by
  unfold losslessSPRetarderEvent diagonalSPEvent diagonalEvent
  exact det2_diagonalEvent_jones
    PolarizationBasis.sp
    OpticalSurfaceKind.totalInternalReflection
    rs rp InfoGeometry.Geometry.KleinFourTag.id

/-! ## 5. Metal mirror as lossy complex retarder / diattenuator -/

/--
A diagonal metal-mirror event in the `s/p` basis.

The coefficients are complex amplitude reflection coefficients. Loss,
retardance, and ellipticity are calibrated downstream.
-/
def metalMirrorEvent
    (rs rp : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    JonesOpticalEvent :=
  diagonalSPEvent OpticalSurfaceKind.metalMirror rs rp tag

/-- A metal mirror event is diattenuating whenever the channel magnitudes differ. -/
theorem metalMirrorEvent_isDiattenuating
    (rs rp : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag)
    (h : ‖rs‖ ≠ ‖rp‖) :
    IsDiattenuating (metalMirrorEvent rs rp tag) := by
  unfold IsDiattenuating metalMirrorEvent diagonalSPEvent diagonalEvent
  exact h

/--
The determinant of a diagonal metal mirror event is the product of the two
complex reflection amplitudes.
-/
theorem det2_metalMirrorEvent_jones
    (rs rp : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    det2 (metalMirrorEvent rs rp tag).jones = rs * rp := by
  unfold metalMirrorEvent diagonalSPEvent diagonalEvent
  exact det2_diagonalEvent_jones
    PolarizationBasis.sp
    OpticalSurfaceKind.metalMirror
    rs rp tag

/-! ## 6. Circular-basis chiral media -/

/-- A diagonal chiral-medium event in the circular `L/R` basis. -/
def chiralMediumEvent
    (rL rR : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    JonesOpticalEvent :=
  diagonalCircularEvent OpticalSurfaceKind.chiralMedium rL rR tag

/-- A circular-birefringent event has unit magnitude in both circular channels. -/
theorem chiralMediumEvent_isCircularBirefringent
    (rL rR : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag)
    (hL : ‖rL‖ = 1)
    (hR : ‖rR‖ = 1) :
    IsCircularBirefringent (chiralMediumEvent rL rR tag) := by
  unfold IsCircularBirefringent chiralMediumEvent diagonalCircularEvent diagonalEvent
  exact ⟨rfl, hL, hR⟩

/-- A circular-dichroic event has different left/right channel magnitudes. -/
theorem chiralMediumEvent_isCircularDichroic
    (rL rR : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag)
    (h : ‖rL‖ ≠ ‖rR‖) :
    IsCircularDichroic (chiralMediumEvent rL rR tag) := by
  unfold IsCircularDichroic chiralMediumEvent diagonalCircularEvent diagonalEvent
  exact ⟨rfl, h⟩

/--
The determinant of a circular-basis chiral medium event is the product of the
left and right circular coefficients.
-/
theorem det2_chiralMediumEvent_jones
    (rL rR : ℂ)
    (tag : InfoGeometry.Geometry.KleinFourTag.Tag) :
    det2 (chiralMediumEvent rL rR tag).jones = rL * rR := by
  unfold chiralMediumEvent diagonalCircularEvent diagonalEvent
  exact det2_diagonalEvent_jones
    PolarizationBasis.circular
    OpticalSurfaceKind.chiralMedium
    rL rR tag

end InfoGeometry.OperatorAlgebra.FiniteJonesOptics
