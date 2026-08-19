/-
InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean

Narrow projective-temperature sidecar.

This file does not introduce a new Möbius theory.  It transports the existing
real upper-half-plane `SL2R` action to the positive-imaginary Souriau
temperature sector.

The projective/closure language is supplied by existing modules:
* `Geometry.RealMoebiusAction`;
* `OperatorAlgebra.MobiusClosureFixedPoints`.
-/

import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints
import InfoGeometry.ProjectiveFoundation

noncomputable section

open scoped MatrixGroups

namespace InfoGeometry.Thermodynamics

open InfoGeometry.Geometry
open InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints

/-! ## 1. Positive Souriau temperatures and the real upper half-plane -/

/--
The positive-height Souriau temperature sector.

This is the part of `SouriauTemperature` whose complex coordinate lies in the
upper half-plane.
-/
abbrev PositiveSouriauTemperature := {s : ℂ // 0 < s.im}

namespace PositiveSouriauTemperature

abbrev temp (T : PositiveSouriauTemperature) : SouriauTemperature := T.1
abbrev im_pos (T : PositiveSouriauTemperature) : 0 < T.temp.s.im := T.2

end PositiveSouriauTemperature

namespace PositiveSouriauTemperature

/-- Forget the thermodynamic packaging and read the temperature as a real UHP point. -/
def toRealUpperHalfPlane
    (T : PositiveSouriauTemperature) :
    RealUpperHalfPlane :=
  (T.temp.s.re, ⟨T.temp.s.im, T.im_pos⟩)

/-- Package a real UHP point as a positive Souriau temperature. -/
def ofRealUpperHalfPlane
    (τ : RealUpperHalfPlane) :
    PositiveSouriauTemperature :=
  ⟨Complex.mk τ.x τ.y, by simpa using τ.y_pos⟩

@[simp]
theorem toRealUpperHalfPlane_x
    (T : PositiveSouriauTemperature) :
    (T.toRealUpperHalfPlane).x = T.temp.s.re :=
  rfl

@[simp]
theorem toRealUpperHalfPlane_y
    (T : PositiveSouriauTemperature) :
    (T.toRealUpperHalfPlane).y = T.temp.s.im :=
  rfl

@[simp]
theorem ofRealUpperHalfPlane_temp_s
    (τ : RealUpperHalfPlane) :
    (ofRealUpperHalfPlane τ).temp.s = Complex.mk τ.x τ.y :=
  rfl

@[simp]
theorem toRealUpperHalfPlane_ofRealUpperHalfPlane
    (τ : RealUpperHalfPlane) :
    toRealUpperHalfPlane (ofRealUpperHalfPlane τ) = τ := by
  ext <;> simp [toRealUpperHalfPlane, ofRealUpperHalfPlane]

@[simp]
theorem ofRealUpperHalfPlane_toRealUpperHalfPlane
    (T : PositiveSouriauTemperature) :
    ofRealUpperHalfPlane (toRealUpperHalfPlane T) = T := by
  apply Subtype.ext
  apply Complex.ext <;> rfl

/-! ## 2. Transported `SL2R` action -/

/-- The `SL2R` lift of the central matrix `-I`. -/
def negIdSL2R : SL2R :=
  ⟨!![-(1 : ℝ), 0; 0, -(1 : ℝ)], by
    norm_num [Matrix.det_fin_two_of]⟩

/--
Transport the existing real `SL2R` Möbius action on `RealUpperHalfPlane` to
positive Souriau temperatures.
-/
instance : MulAction SL2R PositiveSouriauTemperature where
  smul g T :=
    ofRealUpperHalfPlane (g • T.toRealUpperHalfPlane)

  one_smul T := by
    change ofRealUpperHalfPlane
        ((1 : SL2R) • T.toRealUpperHalfPlane) = T
    rw [RealUpperHalfPlane.one_smul_real]
    exact ofRealUpperHalfPlane_toRealUpperHalfPlane T

  mul_smul g h T := by
    change ofRealUpperHalfPlane
        (((g * h) : SL2R) • T.toRealUpperHalfPlane)
      =
        ofRealUpperHalfPlane
          (g • (toRealUpperHalfPlane
            (ofRealUpperHalfPlane (h • T.toRealUpperHalfPlane))))
    rw [toRealUpperHalfPlane_ofRealUpperHalfPlane]
    rw [RealUpperHalfPlane.mul_smul_real]

@[simp]
theorem smul_def
    (g : SL2R)
    (T : PositiveSouriauTemperature) :
    g • T =
      ofRealUpperHalfPlane (g • T.toRealUpperHalfPlane) :=
  rfl

@[simp]
theorem toRealUpperHalfPlane_smul
    (g : SL2R)
    (T : PositiveSouriauTemperature) :
    toRealUpperHalfPlane (g • T) =
      g • T.toRealUpperHalfPlane := by
  simp [smul_def]

/-- The central lift `-I` acts trivially on positive Souriau temperatures. -/
@[simp]
theorem negIdSL2R_smul
    (T : PositiveSouriauTemperature) :
    negIdSL2R • T = T := by
  change ofRealUpperHalfPlane (negIdSL2R • T.toRealUpperHalfPlane) = T
  have h :
      negIdSL2R • T.toRealUpperHalfPlane =
        T.toRealUpperHalfPlane := by
    ext <;>
      simp [negIdSL2R, RealUpperHalfPlane.smul_def, RealUpperHalfPlane.moebius,
        RealUpperHalfPlane.a, RealUpperHalfPlane.b, RealUpperHalfPlane.c,
        RealUpperHalfPlane.d, RealUpperHalfPlane.denomSq]
  rw [h]
  exact ofRealUpperHalfPlane_toRealUpperHalfPlane T

/-! ## 3. Closure and invariant readouts from an involutive cover element -/

/--
A projective/closure temperature inversion supplied by an involutive `SL2R`
element.

This is deliberately property-gated: the sidecar does not assert which matrix is
the physical inversion unless a model supplies it.
-/
abbrev ProjectiveTemperatureInversion :=
  {element : SL2R // element * element = 1}

namespace ProjectiveTemperatureInversion

def negId : ProjectiveTemperatureInversion :=
  ⟨negIdSL2R, by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [negIdSL2R, Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp] theorem negId_element : negId.1 = negIdSL2R := rfl

abbrev element (I : ProjectiveTemperatureInversion) : SL2R := I.1

abbrev element_sq (I : ProjectiveTemperatureInversion) : I.element * I.element = 1 := I.2

/--
The existing abstract closure-involution interface applied to the transported
temperature action.
-/
def closure
    (I : ProjectiveTemperatureInversion) :
    ClosureInvolution PositiveSouriauTemperature where
  theta T := I.element • T
  theta_sq T := by
    calc
      I.element • (I.element • T)
          = (I.element * I.element) • T := by
              rw [← mul_smul]
      _ = (1 : SL2R) • T := by
              rw [I.element_sq]
      _ = T := by
              rw [one_smul]

@[simp]
theorem closure_theta
    (I : ProjectiveTemperatureInversion)
    (T : PositiveSouriauTemperature) :
    (I.closure).theta T = I.element • T :=
  rfl

/--
Invariant temperature readouts are expressed through the existing
`InvariantReadout` interface, not by adding a new invariance structure.
-/
abbrev InvariantTemperatureReadout
    (I : ProjectiveTemperatureInversion)
    (Charge : Type) :
    Type :=
  InvariantReadout PositiveSouriauTemperature Charge I.closure

/-- The readout is unchanged by the supplied temperature inversion. -/
theorem read_theta
    {I : ProjectiveTemperatureInversion}
    {Charge : Type}
    (R : I.InvariantTemperatureReadout Charge)
    (T : PositiveSouriauTemperature) :
    R.read ((I.closure).theta T) = R.read T :=
  R.read_theta T

/-! ## 4. Stationary temperatures -/

/--
A positive Souriau temperature is stationary for a supplied projective
temperature inversion when it is fixed by the associated closure involution.

This is deliberately relative to the supplied inversion property.  In
particular, no specific matrix such as the modular `S` element is asserted here.
-/
def StationaryTemperature
    (I : ProjectiveTemperatureInversion)
    (T : PositiveSouriauTemperature) : Prop :=
  I.closure.IsFixed T

theorem negId_stationary (T : PositiveSouriauTemperature) :
    StationaryTemperature negId T := by
  change negIdSL2R • T = T
  exact negIdSL2R_smul T

/-- Equivalently, the supplied `SL2R` element fixes a stationary temperature. -/
theorem smul_eq_self_of_stationary
    {I : ProjectiveTemperatureInversion}
    {T : PositiveSouriauTemperature}
    (hT : StationaryTemperature I T) :
    I.element • T = T := by
  simpa [StationaryTemperature, closure, ClosureInvolution.IsFixed] using hT

/-- Invariant readouts are unchanged by the supplied lift action. -/
theorem read_lift
    {I : ProjectiveTemperatureInversion}
    {Charge : Type}
    (R : I.InvariantTemperatureReadout Charge)
    (T : PositiveSouriauTemperature) :
    R.read (I.element • T) = R.read T := by
  simpa [closure] using R.read_theta T

/-- Any readout is unchanged at a stationary temperature after applying the closure. -/
theorem read_eq_of_stationary
    {I : ProjectiveTemperatureInversion}
    {Charge : Type}
    (read : PositiveSouriauTemperature → Charge)
    {T : PositiveSouriauTemperature}
    (hT : StationaryTemperature I T) :
    read ((I.closure).theta T) = read T := by
  rw [hT]

end ProjectiveTemperatureInversion

/-! ## 5. Projective involutions represented by `±I` lift squares -/

/--
A lift-level projective temperature inversion supplied by an `SL2R` element
whose square is either `I` or `-I`.

This is the concrete interface for matrices such as the modular `S` element:
`S^2 = -I` in `SL2R`, but `-I` acts trivially on the upper half-plane.
-/
abbrev ProjectiveLiftTemperatureInversion :=
  {element : SL2R // element * element = 1 ∨ element * element = negIdSL2R}

namespace ProjectiveLiftTemperatureInversion

abbrev element (I : ProjectiveLiftTemperatureInversion) : SL2R := I.1

abbrev element_sq_lift (I : ProjectiveLiftTemperatureInversion) :
    I.element * I.element = 1 ∨ I.element * I.element = negIdSL2R := I.2

/-- The lift square acts trivially on positive Souriau temperatures. -/
theorem smul_trivial_of_projective_sq
    (I : ProjectiveLiftTemperatureInversion)
    (T : PositiveSouriauTemperature) :
    (I.element * I.element) • T = T := by
  rcases I.element_sq_lift with h | h
  · rw [h, one_smul]
  · rw [h]
    exact negIdSL2R_smul T

/--
The abstract closure-involution interface applied to the projective lift action.
-/
def closure
    (I : ProjectiveLiftTemperatureInversion) :
    ClosureInvolution PositiveSouriauTemperature where
  theta T := I.element • T
  theta_sq T := by
    calc
      I.element • (I.element • T)
          = (I.element * I.element) • T := by
              rw [← mul_smul]
      _ = T := I.smul_trivial_of_projective_sq T

@[simp]
theorem closure_theta
    (I : ProjectiveLiftTemperatureInversion)
    (T : PositiveSouriauTemperature) :
    (I.closure).theta T = I.element • T :=
  rfl

/-- Invariant readouts for a lift-level projective temperature inversion. -/
abbrev InvariantTemperatureReadout
    (I : ProjectiveLiftTemperatureInversion)
    (Charge : Type) :
    Type :=
  InvariantReadout PositiveSouriauTemperature Charge I.closure

/-- The readout is unchanged by the supplied lift-level projective inversion. -/
theorem read_theta
    {I : ProjectiveLiftTemperatureInversion}
    {Charge : Type}
    (R : I.InvariantTemperatureReadout Charge)
    (T : PositiveSouriauTemperature) :
    R.read ((I.closure).theta T) = R.read T :=
  R.read_theta T

/-- Stationary temperatures for the supplied lift-level projective inversion. -/
def StationaryTemperature
    (I : ProjectiveLiftTemperatureInversion)
    (T : PositiveSouriauTemperature) : Prop :=
  I.closure.IsFixed T

/-- A stationary temperature is fixed by the projective lift action. -/
theorem smul_eq_self_of_stationary
    {I : ProjectiveLiftTemperatureInversion}
    {T : PositiveSouriauTemperature}
    (hT : StationaryTemperature I T) :
    I.element • T = T := by
  simpa [StationaryTemperature, closure, ClosureInvolution.IsFixed] using hT

/-- Invariant readouts are unchanged by the supplied lift action. -/
theorem read_lift
    {I : ProjectiveLiftTemperatureInversion}
    {Charge : Type}
    (R : I.InvariantTemperatureReadout Charge)
    (T : PositiveSouriauTemperature) :
    R.read (I.element • T) = R.read T := by
  simpa [closure] using R.read_theta T

/-- Any readout is unchanged at a stationary temperature after applying the closure. -/
theorem read_eq_of_stationary
    {I : ProjectiveLiftTemperatureInversion}
    {Charge : Type}
    (read : PositiveSouriauTemperature → Charge)
    {T : PositiveSouriauTemperature}
    (hT : StationaryTemperature I T) :
    read ((I.closure).theta T) = read T := by
  rw [hT]

end ProjectiveLiftTemperatureInversion

/-! ## 6. Projective inversions in the `PSL2R` quotient -/

/--
A projective temperature inversion represented by an `SL2R` lift whose square
is trivial after descending to `PSL2R`.

This is the correct interface for matrices such as the modular `S` element:
upstairs in `SL2R` one has `S^2 = -I`, while downstairs in `PSL2R` this becomes
an involution.
-/
structure ProjectivePSLTemperatureInversion where
  /-- A chosen `SL2R` lift of the projective inversion. -/
  element : SL2R

  /-- The lift squares to the identity in the projective quotient. -/
  element_sq_projective :
    InfoGeometry.ProjectiveFoundation.sl2rToPSL2R (element * element) = 1

  /--
  Model-supplied projective action on positive Souriau temperatures.

  This is deliberately supplied as data: the sidecar does not prove the
  quotient action is independent of the chosen lift.
  -/
  projectiveTheta : PositiveSouriauTemperature → PositiveSouriauTemperature

  /-- The supplied projective action agrees with the chosen lift. -/
  projectiveTheta_eq_lift :
    ∀ T : PositiveSouriauTemperature, projectiveTheta T = element • T

  /-- The supplied projective action is an involution. -/
  projectiveTheta_sq :
    ∀ T : PositiveSouriauTemperature, projectiveTheta (projectiveTheta T) = T

namespace ProjectivePSLTemperatureInversion

/--
The abstract closure involution attached to a projective temperature inversion.
-/
def closure
    (I : ProjectivePSLTemperatureInversion) :
    ClosureInvolution PositiveSouriauTemperature where
  theta := I.projectiveTheta
  theta_sq := I.projectiveTheta_sq

@[simp]
theorem closure_theta
    (I : ProjectivePSLTemperatureInversion)
    (T : PositiveSouriauTemperature) :
    (I.closure).theta T = I.projectiveTheta T :=
  rfl

/-- The projective closure agrees with the chosen `SL2R` lift action. -/
theorem closure_theta_eq_lift
    (I : ProjectivePSLTemperatureInversion)
    (T : PositiveSouriauTemperature) :
    (I.closure).theta T = I.element • T :=
  I.projectiveTheta_eq_lift T

/-- Invariant readouts for a projective `PSL2R` temperature inversion. -/
abbrev InvariantTemperatureReadout
    (I : ProjectivePSLTemperatureInversion)
    (Charge : Type) :
    Type :=
  InvariantReadout PositiveSouriauTemperature Charge I.closure

/-- The readout is unchanged by the supplied projective inversion. -/
theorem read_theta
    {I : ProjectivePSLTemperatureInversion}
    {Charge : Type}
    (R : I.InvariantTemperatureReadout Charge)
    (T : PositiveSouriauTemperature) :
    R.read ((I.closure).theta T) = R.read T :=
  R.read_theta T

/--
The chosen lift square acts trivially because the supplied projective action is
involutive.
-/
theorem lift_square_smul_eq_self
    (I : ProjectivePSLTemperatureInversion)
    (T : PositiveSouriauTemperature) :
    (I.element * I.element) • T = T := by
  calc
    (I.element * I.element) • T
        = I.element • (I.element • T) := by
            rw [mul_smul]
    _ = I.projectiveTheta (I.element • T) := by
            rw [I.projectiveTheta_eq_lift (I.element • T)]
    _ = I.projectiveTheta (I.projectiveTheta T) := by
            rw [I.projectiveTheta_eq_lift T]
    _ = T :=
            I.projectiveTheta_sq T

/-- Stationary temperatures for the supplied projective inversion. -/
def StationaryTemperature
    (I : ProjectivePSLTemperatureInversion)
    (T : PositiveSouriauTemperature) : Prop :=
  I.closure.IsFixed T

/-- A stationary temperature is fixed by the chosen lift action. -/
theorem smul_eq_self_of_stationary
    {I : ProjectivePSLTemperatureInversion}
    {T : PositiveSouriauTemperature}
    (hT : StationaryTemperature I T) :
    I.element • T = T := by
  rw [← I.closure_theta_eq_lift T]
  exact hT

end ProjectivePSLTemperatureInversion

end PositiveSouriauTemperature

end InfoGeometry.Thermodynamics
