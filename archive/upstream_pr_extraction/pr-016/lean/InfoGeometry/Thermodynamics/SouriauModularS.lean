/-
InfoGeometry/Thermodynamics/SouriauModularS.lean

Concrete modular `S` lift for positive Souriau temperatures.

This sidecar installs the standard matrix

  S = [[0, -1], [1, 0]]

as an `SL2R` lift whose square is the named central lift `negIdSL2R`.  Since
that lift acts trivially on the real upper half-plane, the existing
`ProjectiveLiftTemperatureInversion` socket turns this into a genuine closure
involution on positive Souriau temperatures.

The file does not claim a modular-form theorem, KMS existence theorem, or a
global Bost-Connes phase transition.  It provides only the concrete projective
temperature inversion anchor used by downstream routing/orchestration.
-/

import InfoGeometry.Thermodynamics.SouriauTemperatureProjective

noncomputable section

open scoped MatrixGroups

namespace InfoGeometry.Thermodynamics

open InfoGeometry.Geometry

namespace PositiveSouriauTemperature

/-! ## 1. The concrete modular `S` lift -/

/-- The standard modular `S` matrix, viewed as an `SL(2,ℝ)` lift. -/
def modularS : SL2R :=
  ⟨!![(0 : ℝ), -1; 1, 0], by
    norm_num [Matrix.det_fin_two_of]⟩

/-- The modular `S` lift squares to the central element `-I`. -/
theorem modularS_sq :
    modularS * modularS = negIdSL2R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularS, negIdSL2R, Matrix.mul_apply]

/--
The standard modular `S` projective lift.

This is the certified Lean anchor for the physical inversion `τ ↦ -1 / τ`.
-/
def modularSLiftInversion : ProjectiveLiftTemperatureInversion where
  element := modularS
  element_sq_lift := Or.inr modularS_sq

@[simp]
theorem modularSLiftInversion_element :
    modularSLiftInversion.element = modularS :=
  rfl

/-! ## 2. The fixed temperature `i` -/

/-- The unit imaginary positive Souriau temperature. -/
def unitImaginary : PositiveSouriauTemperature where
  temp := { s := Complex.I }
  im_pos := by
    norm_num [Complex.I]

@[simp]
theorem unitImaginary_re :
    unitImaginary.temp.s.re = 0 := by
  norm_num [unitImaginary, Complex.I]

@[simp]
theorem unitImaginary_im :
    unitImaginary.temp.s.im = 1 := by
  norm_num [unitImaginary, Complex.I]

/-- The modular `S` lift fixes the unit imaginary temperature. -/
theorem modularS_smul_unitImaginary :
    modularS • unitImaginary = unitImaginary := by
  have h :
      toRealUpperHalfPlane (modularS • unitImaginary) =
        toRealUpperHalfPlane unitImaginary := by
    ext <;>
      simp [unitImaginary, modularS, smul_def, ofRealUpperHalfPlane,
        toRealUpperHalfPlane, RealUpperHalfPlane.smul_def,
        RealUpperHalfPlane.moebius, RealUpperHalfPlane.a,
        RealUpperHalfPlane.b, RealUpperHalfPlane.c, RealUpperHalfPlane.d,
        RealUpperHalfPlane.denomSq]
  calc
    modularS • unitImaginary
        = ofRealUpperHalfPlane
            (toRealUpperHalfPlane (modularS • unitImaginary)) := by
            rw [ofRealUpperHalfPlane_toRealUpperHalfPlane]
    _ = ofRealUpperHalfPlane (toRealUpperHalfPlane unitImaginary) := by
            rw [h]
    _ = unitImaginary := by
            rw [ofRealUpperHalfPlane_toRealUpperHalfPlane]

/-- The unit imaginary temperature is stationary for the modular `S` lift. -/
theorem unitImaginary_stationary_modularS :
    ProjectiveLiftTemperatureInversion.StationaryTemperature
      modularSLiftInversion unitImaginary := by
  simpa [ProjectiveLiftTemperatureInversion.StationaryTemperature,
    ProjectiveLiftTemperatureInversion.closure, modularSLiftInversion] using
    modularS_smul_unitImaginary

/-- The modular `S` closure fixes the unit imaginary temperature. -/
theorem modularS_closure_unitImaginary :
    (modularSLiftInversion.closure).theta unitImaginary = unitImaginary := by
  simpa [ProjectiveLiftTemperatureInversion.closure, modularSLiftInversion] using
    modularS_smul_unitImaginary

/-! ## 3. Owner target -/

/--
Installed owner target for the concrete modular `S` temperature anchor.

The payload is deliberately finite and geometric:

* `S² = negIdSL2R` in `SL2R`;
* `S` is accepted by the projective-lift inversion socket;
* the unit imaginary temperature is stationary under that lift.
-/
def ModularSTemperatureOwnerTarget : Prop :=
  modularS * modularS = negIdSL2R ∧
    modularSLiftInversion.element = modularS ∧
    ProjectiveLiftTemperatureInversion.StationaryTemperature
      modularSLiftInversion unitImaginary

/-- The installed modular `S` owner target follows from the concrete witness. -/
theorem modularSTemperatureOwnerTarget :
    ModularSTemperatureOwnerTarget := by
  exact ⟨modularS_sq, rfl, unitImaginary_stationary_modularS⟩

end PositiveSouriauTemperature

end InfoGeometry.Thermodynamics
