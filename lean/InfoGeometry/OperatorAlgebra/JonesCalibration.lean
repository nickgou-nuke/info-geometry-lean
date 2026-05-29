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

import Mathlib
import InfoGeometry.OperatorAlgebra.TopologicalSnap

noncomputable section

namespace InfoGeometry.OperatorAlgebra.JonesCalibration

open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. V₄ orientation tags -/

/--
Discrete V₄-style orientation tag.

`parity = true` records a spatial/parity flip.

`time = true` records a propagation/time-orientation reversal tag.
-/
structure V4Tag where
  parity : Bool
  time : Bool
deriving DecidableEq, Repr

namespace V4Tag

/-- Identity sector. -/
def id : V4Tag :=
  ⟨false, false⟩

/-- Parity/spatial-reflection sector. -/
def P : V4Tag :=
  ⟨true, false⟩

/-- Time/propagation-reversal sector. -/
def T : V4Tag :=
  ⟨false, true⟩

/-- Combined PT sector. -/
def PT : V4Tag :=
  ⟨true, true⟩

end V4Tag

/-! ## 2. Jones matrices and polarization bases -/

/-- Jones vectors for a two-channel polarization basis. -/
abbrev JonesVec :=
  Fin 2 → ℂ

/-- Jones matrices for a two-channel polarization basis. -/
abbrev JonesMat :=
  Matrix (Fin 2) (Fin 2) ℂ

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
  fun i j =>
    if i = j then
      if i = 0 then a else b
    else 0

/-- The `s`-channel projector in the `s/p` basis. -/
def sProjector : JonesMat :=
  diagJones 1 0

/-- The `p`-channel projector in the `s/p` basis. -/
def pProjector : JonesMat :=
  diagJones 0 1

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

  /--
  Coherence law.

  If the event is strongly depolarizing, a Stokes/Mueller/channel model should
  replace ordinary Jones calculus.
  -/
  coherence_law : Prop

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
A calibration saying how an optical event's V₄ tag should be interpreted.

The tag does not determine the continuous coefficients. It records the
orientation/PT bookkeeping attached to the event.
-/
structure V4OpticalCalibration where
  /-- Event being calibrated. -/
  event : JonesOpticalEvent

  /-- Interpretation law for the V₄ tag. -/
  tag_law : Prop

  /--
  Optical channel law.

  This is where a concrete module may say, for example, that a metal mirror is
  represented by a PT-tagged lossy retarder, or that Brewster reflection is a
  rank-collapse boundary event.
  -/
  channel_law : Prop

/--
A Brewster calibration packages an event with its rank-collapse proof.
-/
structure BrewsterCalibration where
  event : JonesOpticalEvent
  is_brewster : IsBrewsterEvent event

/--
A total-internal-reflection calibration packages a lossless retarder event.
-/
structure TIRCalibration where
  event : JonesOpticalEvent
  is_lossless : IsLosslessRetarder event
  tir_law : Prop

/--
A metal-mirror calibration packages a possibly lossy complex retarder.
-/
structure MetalMirrorCalibration where
  event : JonesOpticalEvent
  metal_law : Prop

  /-- Optional statement that the event is diattenuating. -/
  diattenuation_law : Prop

/--
A chiral-medium calibration packages circular-basis transport.
-/
structure ChiralMediumCalibration where
  event : JonesOpticalEvent
  circular_basis :
    event.basis = PolarizationBasis.circular

  chiral_transport_law : Prop

/-! ## 6. Topological obstruction link -/

/--
An optical event may carry a topological/anomaly obstruction charge.

This is the bridge from Jones/Fresnel optics into `TopologicalSnap`.
-/
structure JonesObstructionCalibration
    (State Charge : Type*) [Zero Charge] where
  /-- Optical event assigned to a state. -/
  eventOf : State → JonesOpticalEvent

  /-- Obstruction charge assigned to a state. -/
  obstruction : State → Charge

  /-- Flat optical sector. -/
  Flat : Set State

  /--
  Flat optical states have trivial obstruction.
  -/
  flat_obstruction_zero :
    ∀ x : State, x ∈ Flat → obstruction x = 0

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

  /-- Divisor/counting law, left abstract at this layer. -/
  divisor_law : Prop

end InfoGeometry.OperatorAlgebra.JonesCalibration
