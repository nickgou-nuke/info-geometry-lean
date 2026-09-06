/-
InfoGeometry/OperatorAlgebra/JonesCalibration.lean

Jones/Fresnel calibration for operatorial optical surfaces.

This module connects:

* continuous Jones/Fresnel optical coefficients;
* discrete V₄ orientation tags;
* surface classes such as Brewster, total internal reflection, metal mirrors,
  chiral media, rough depolarizing surfaces, and metasurfaces;
* topological obstruction readouts usable by `TopologicalSnap`.

The Fresnel coefficients are not themselves V₄ elements. They are continuous
weights attached to polarization channels. The V₄ tag records discrete
orientation/PT bookkeeping.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.TopologicalSnap
import InfoGeometry.Geometry.KleinFourTag
import InfoGeometry.Optics.FiniteJonesModel

noncomputable section

namespace InfoGeometry.OperatorAlgebra.JonesCalibration

open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. V₄ orientation tags -/

/-- Canonical Klein-four parity/time orientation tag. -/
abbrev V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.Tag

namespace V4Tag

/-- Identity sector. -/
def id : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.id

/-- Parity/spatial-reflection sector. -/
def P : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.P

/-- Time/propagation-reversal sector. -/
def T : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.T

/-- Combined PT sector. -/
def PT : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.PT

end V4Tag

/-! ## 2. Jones matrices and polarization bases -/

/-- Jones vectors for a two-channel polarization basis. -/
abbrev JonesVec :=
  Fin 2 → ℂ

/-- Jones matrices for a two-channel polarization basis. -/
abbrev JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.JonesMat

/--
Polarization basis used by a local optical description.
-/
inductive PolarizationBasis where
  /-- Fresnel basis: `0 = s`, `1 = p`. -/
  | sp
  /-- Circular/chiral basis: `0 = L`, `1 = R`. -/
  | circular
deriving DecidableEq, Repr

/--
Diagonal Jones matrix.

In the `s/p` basis, this is `diag(r_s, r_p)`.

In the circular `L/R` basis, this is `diag(r_L, r_R)`.
-/
def diagJones
    (a b : ℂ) : JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.diagJones a b

/-- The `s`-channel projector in the `s/p` basis. -/
def sProjector : JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.sProjector

/-- The `p`-channel projector in the `s/p` basis. -/
def pProjector : JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.pProjector

/-- The `L`-channel projector in the circular basis. -/
def leftCircularProjector : JonesMat :=
  diagJones 1 0

/-- The `R`-channel projector in the circular basis. -/
def rightCircularProjector : JonesMat :=
  diagJones 0 1

/-! ## 3. Optical surface classes -/

/--
Surface/interface kind for Jones calibration.
-/
inductive OpticalSurfaceKind where
  /-- Smooth transparent dielectric reflection. -/
  | dielectricReflection
  /-- Brewster-angle rank collapse. -/
  | brewsterProjection
  /-- Total internal reflection / lossless retarder. -/
  | totalInternalReflection
  /-- Metal mirror / lossy complex retarder. -/
  | metalMirror
  /-- Chiral medium / circular birefringence or dichroism. -/
  | chiralMedium
  /-- Rough/depolarizing surface; Jones calculus may be insufficient. -/
  | roughDepolarizingSurface
  /-- Structured anisotropic/metasurface interface. -/
  | metasurface
  /-- Abstract calibrated optical event. -/
  | abstract
deriving DecidableEq, Repr

/--
A coherent Jones-calibrated optical event.

`coeff0` and `coeff1` are basis-dependent:

* in the `s/p` basis: `coeff0 = r_s`, `coeff1 = r_p`;
* in the circular basis: `coeff0 = r_L`, `coeff1 = r_R`.

The `tag` records the discrete V₄ orientation bookkeeping.
-/
structure JonesOpticalEvent where
  basis : PolarizationBasis
  kind : OpticalSurfaceKind
  coeff0 : ℂ
  coeff1 : ℂ
  tag : V4Tag

namespace JonesOpticalEvent

/-- Jones matrix of a calibrated optical event. -/
def jones
    (E : JonesOpticalEvent) : JonesMat :=
  diagJones E.coeff0 E.coeff1

/-- The first diagonal Jones entry is the first calibrated coefficient. -/
@[simp]
theorem jones_apply_same_zero
    (E : JonesOpticalEvent) :
    E.jones 0 0 = E.coeff0 := by
  simp [jones, diagJones]

/-- The second diagonal Jones entry is the second calibrated coefficient. -/
@[simp]
theorem jones_apply_same_one
    (E : JonesOpticalEvent) :
    E.jones 1 1 = E.coeff1 := by
  simp [jones, diagJones]

/-- The upper-right Jones entry vanishes for diagonal calibrated events. -/
@[simp]
theorem jones_apply_offdiag_zero_one
    (E : JonesOpticalEvent) :
    E.jones 0 1 = 0 := by
  simp [jones, diagJones]

/-- The lower-left Jones entry vanishes for diagonal calibrated events. -/
@[simp]
theorem jones_apply_offdiag_one_zero
    (E : JonesOpticalEvent) :
    E.jones 1 0 = 0 := by
  simp [jones, diagJones]

/-- First-channel coefficient. In `s/p`, this is `r_s`; in circular, `r_L`. -/
def firstCoeff
    (E : JonesOpticalEvent) : ℂ :=
  E.coeff0

/-- Second-channel coefficient. In `s/p`, this is `r_p`; in circular, `r_R`. -/
def secondCoeff
    (E : JonesOpticalEvent) : ℂ :=
  E.coeff1

end JonesOpticalEvent

/-! ## 4. Fresnel/Brewster/TIR/metal/chiral predicates -/

/--
A Brewster event in the `s/p` basis.

The `p` reflection channel vanishes while the `s` channel is nonzero.
-/
def IsBrewsterEvent
    (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.sp ∧
  E.kind = OpticalSurfaceKind.brewsterProjection ∧
  E.coeff1 = 0 ∧
  E.coeff0 ≠ 0

/--
A lossless retarder.

Both channels have unit magnitude. This includes idealized total internal
reflection and ideal waveplate behavior.
-/
def IsLosslessRetarder
    (E : JonesOpticalEvent) : Prop :=
  ‖E.coeff0‖ = 1 ∧
  ‖E.coeff1‖ = 1

/--
A diattenuating event.

The two basis channels have different magnitudes.
-/
def IsDiattenuating
    (E : JonesOpticalEvent) : Prop :=
  ‖E.coeff0‖ ≠ ‖E.coeff1‖

/--
A circular-birefringent event.

In the circular basis, the two handedness channels acquire unit-magnitude
phase factors.
-/
def IsCircularBirefringent
    (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.circular ∧
  ‖E.coeff0‖ = 1 ∧
  ‖E.coeff1‖ = 1

/--
A circular-dichroic event.

In the circular basis, left and right handedness have different attenuation.
-/
def IsCircularDichroic
    (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.circular ∧
  ‖E.coeff0‖ ≠ ‖E.coeff1‖

namespace JonesOpticalEvent

/--
At Brewster calibration, the second channel coefficient vanishes.
-/
theorem brewster_secondCoeff_zero
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.secondCoeff = 0 :=
  hE.2.2.1

/--
At Brewster calibration, the first channel coefficient is nonzero.
-/
theorem brewster_firstCoeff_ne_zero
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.firstCoeff ≠ 0 :=
  hE.2.2.2

end JonesOpticalEvent

/-! ## 5. V₄-to-optical calibration -/

/--
A V₄ optical calibration is the event itself: its canonical Klein-four tag is
already part of `JonesOpticalEvent`.
-/
abbrev V4OpticalCalibration :=
  JonesOpticalEvent

/--
A Brewster calibration is the native subtype of events satisfying the
rank-collapse predicate.
-/
abbrev BrewsterCalibration :=
  {event : JonesOpticalEvent // IsBrewsterEvent event}

namespace BrewsterCalibration

/-- Underlying calibrated event. -/
def event (C : BrewsterCalibration) : JonesOpticalEvent :=
  C.1

/-- The underlying event satisfies the Brewster predicate. -/
theorem is_brewster (C : BrewsterCalibration) :
    IsBrewsterEvent C.event :=
  C.2

end BrewsterCalibration

/--
A total-internal-reflection calibration is the subtype of lossless events.
-/
abbrev TIRCalibration :=
  {event : JonesOpticalEvent // IsLosslessRetarder event}

namespace TIRCalibration

def event (C : TIRCalibration) : JonesOpticalEvent :=
  C.1

theorem is_lossless (C : TIRCalibration) :
    IsLosslessRetarder C.event :=
  C.2

end TIRCalibration

/--
A metal-mirror calibration packages a possibly lossy complex retarder event.

Concrete material equations belong to the material-response owner file.
-/
abbrev MetalMirrorCalibration :=
  JonesOpticalEvent

/--
A chiral-medium calibration packages the exact circular-basis readout.
-/
abbrev ChiralMediumCalibration :=
  {event : JonesOpticalEvent //
    event.basis = PolarizationBasis.circular}

namespace ChiralMediumCalibration

def event (C : ChiralMediumCalibration) : JonesOpticalEvent :=
  C.1

theorem circular_basis (C : ChiralMediumCalibration) :
    C.event.basis = PolarizationBasis.circular :=
  C.2

end ChiralMediumCalibration

/-! ## 6. Topological obstruction link -/

/--
An optical event assignment together with its obstruction charge.  The flat
sector is derived as the exact zero locus of the obstruction rather than stored
with a separate proof field.
-/
abbrev JonesObstructionCalibration
    (State Charge : Type*) [Zero Charge] :=
  (State → JonesOpticalEvent) × (State → Charge)

namespace JonesObstructionCalibration

/-- Optical event assigned to a state. -/
def eventOf
    {State Charge : Type*} [Zero Charge]
    (C : JonesObstructionCalibration State Charge) :
    State → JonesOpticalEvent :=
  C.1

/-- Obstruction charge assigned to a state. -/
def obstruction
    {State Charge : Type*} [Zero Charge]
    (C : JonesObstructionCalibration State Charge) :
    State → Charge :=
  C.2

/-- The flat optical sector is the obstruction's zero locus. -/
def Flat
    {State Charge : Type*} [Zero Charge]
    (C : JonesObstructionCalibration State Charge) : Set State :=
  {x | C.obstruction x = 0}

theorem flat_obstruction_zero
    {State Charge : Type*} [Zero Charge]
    (C : JonesObstructionCalibration State Charge)
    (x : State) (hx : x ∈ C.Flat) :
    C.obstruction x = 0 :=
  hx

end JonesObstructionCalibration

/--
A Jones obstruction calibration can generate a conserved-obstruction flow once
an admissible flow preserving the obstruction is supplied.
-/
def conservedObstructionFlowOfJones
    (State Charge : Type*) [Zero Charge]
    (C : JonesObstructionCalibration State Charge)
    (flow : ℝ → State → State)
    (hflow : ∀ t x, C.obstruction (flow t x) = C.obstruction x) :
    ConservedObstructionFlow State Charge where
  invariant := C.obstruction
  Flat := C.Flat
  flow := flow
  flat_invariant_zero := C.flat_obstruction_zero
  flow_preserves_invariant := hflow

/-! ## 7. Discrete divisor/index link for arithmetic spectra -/

/--
A spectral divisor socket.

This is the right way to connect discrete zeroes, including zeta/L-function
zeroes, to an integer obstruction charge. The zeroes themselves are complex
locations; the charge is a multiplicity/counting/index readout.
-/
structure SpectralDivisorCharge where
  /-- Zero/divisor locus. -/
  zeroLocus : Set ℂ

  /-- Integer multiplicity/readout. -/
  multiplicity : ℂ → ℤ

  /-- Charge extracted from a region or contour label. -/
  chargeOf : Set ℂ → ℤ

end InfoGeometry.OperatorAlgebra.JonesCalibration
