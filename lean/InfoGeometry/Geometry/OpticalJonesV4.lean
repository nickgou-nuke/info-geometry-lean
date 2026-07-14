/-
InfoGeometry/Geometry/OpticalJonesV4.lean

Operatorial Jones calculus with V4 orientation tags.

The Fresnel/Jones coefficients are continuous optical data.  The V4 tag records
the discrete orientation/parity/time-reversal bookkeeping of the event.
-/

import Mathlib

noncomputable section

namespace OpticalJonesV4

/-! ## 1. V4 orientation tags -/

/--
Discrete orientation tag.

`parity = true` records a spatial/parity flip.
`time = true` records time/propagation-orientation reversal bookkeeping.
-/
structure V4Tag where
  parity : Bool
  time : Bool
deriving DecidableEq, Repr

namespace V4Tag

/-- Identity sector. -/
def id : V4Tag :=
  ⟨false, false⟩

/-- Parity/spatial reflection sector. -/
def P : V4Tag :=
  ⟨true, false⟩

/-- Time/propagation-reversal sector. -/
def T : V4Tag :=
  ⟨false, true⟩

/-- Combined PT sector. -/
def PT : V4Tag :=
  ⟨true, true⟩

end V4Tag

/-! ## 2. Jones matrices -/

/-- Two-component Jones vector. -/
abbrev JonesVec :=
  Fin 2 → ℂ

/-- Two-by-two Jones matrix. -/
abbrev JonesMat :=
  Matrix (Fin 2) (Fin 2) ℂ

/--
Diagonal Jones matrix.

The convention is index `0 = s` or `L`, index `1 = p` or `R`, depending on
the chosen basis.
-/
def diagJones
    (a b : ℂ) : JonesMat :=
  fun i j =>
    if i = j then
      if i = 0 then a else b
    else 0

/-- The `s`-sector projector in the Fresnel `s/p` basis. -/
def sProjector : JonesMat :=
  diagJones 1 0

/-- The `p`-sector projector in the Fresnel `s/p` basis. -/
def pProjector : JonesMat :=
  diagJones 0 1

/-! ## 3. Fresnel reflection events -/

/--
A Fresnel reflection event in the `s/p` basis.

`rs` and `rp` are the complex Fresnel amplitude reflection coefficients.
`tag` records the discrete orientation bookkeeping of the event.
-/
structure FresnelReflection where
  /-- Complex `s`-polarized reflection coefficient. -/
  rs : ℂ

  /-- Complex `p`-polarized reflection coefficient. -/
  rp : ℂ

  /-- Discrete V4 orientation tag. -/
  tag : V4Tag

namespace FresnelReflection

/-- Jones matrix of a Fresnel reflection in the `s/p` basis. -/
def jones
    (R : FresnelReflection) : JonesMat :=
  diagJones R.rs R.rp

end FresnelReflection

/-- Brewster event: the `p` reflection channel vanishes. -/
def IsBrewsterReflection
    (R : FresnelReflection) : Prop :=
  R.rp = 0 ∧ R.rs ≠ 0

/-- Total-internal-reflection-like retarder: both channels have unit magnitude. -/
def IsLosslessRetarder
    (R : FresnelReflection) : Prop :=
  ‖R.rs‖ = 1 ∧ ‖R.rp‖ = 1

/-- Diattenuation: the two polarization channels have different magnitudes. -/
def IsDiattenuating
    (R : FresnelReflection) : Prop :=
  ‖R.rs‖ ≠ ‖R.rp‖

/--
Scaled projector event.

This captures the Brewster pattern `R_B = c P_s` without forcing the raw
Jones matrix itself to be idempotent.
-/
structure ScaledProjectorEvent where
  /-- Scalar optical coefficient. -/
  scale : ℂ

  /-- Projector channel. -/
  projector : JonesMat

  /-- Matrix realized by the event. -/
  matrix : JonesMat

  /-- Scaled-projector law. -/
  matrix_eq_scaled_projector :
    matrix = scale • projector

/-! ## 4. Circular/chiral transport -/

/--
Transport in the circular `L/R` basis.

A chiral medium is diagonal in this basis when it has circular birefringence or
circular dichroism.
-/
structure CircularTransport where
  /-- Left-circular channel coefficient. -/
  lCoeff : ℂ

  /-- Right-circular channel coefficient. -/
  rCoeff : ℂ

  /-- Discrete V4 orientation tag. -/
  tag : V4Tag

namespace CircularTransport

/-- Jones matrix in the circular `L/R` basis. -/
def jones
    (C : CircularTransport) : JonesMat :=
  diagJones C.lCoeff C.rCoeff

end CircularTransport

/-- Pure circular birefringence: both channels have unit magnitude. -/
def IsCircularBirefringence
    (C : CircularTransport) : Prop :=
  ‖C.lCoeff‖ = 1 ∧ ‖C.rCoeff‖ = 1

/-- Circular dichroism: left and right circular channels have different magnitudes. -/
def IsCircularDichroism
    (C : CircularTransport) : Prop :=
  ‖C.lCoeff‖ ≠ ‖C.rCoeff‖

/-! ## 5. Operatorial Jones connection events -/

/--
Classification of the optical event represented by a local Jones transport.
-/
inductive OpticalEventKind where
  | dielectricReflection
  | brewsterReflection
  | totalInternalReflection
  | metalMirror
  | chiralMedium
  | modularMirror
  | roughDepolarizingSurface
  | abstractCoherentTransport
deriving DecidableEq, Repr

/--
A local operatorial Jones connection event.

This packages a Jones matrix with its discrete V4 orientation tag.  The
`coherent` field is the witness that Jones calculus is the right local model;
if it fails, a concrete theory should use Stokes/Mueller or quantum-channel
data instead.
-/
structure JonesTransport where
  /-- Continuous Jones/Fresnel operator. -/
  matrix : JonesMat

  /-- Discrete orientation/PT/parity bookkeeping. -/
  tag : V4Tag

  /-- Optical event type. -/
  kind : OpticalEventKind

  /-- Coherence certificate for using Jones calculus. -/
  coherent : Prop

/-- A Fresnel reflection supplies a diagonal `s/p` Jones transport. -/
def fresnelJonesTransport
    (R : FresnelReflection) : JonesTransport where
  matrix := R.jones
  tag := R.tag
  kind := OpticalEventKind.dielectricReflection
  coherent := R.jones 0 1 = 0 ∧ R.jones 1 0 = 0

/-- A Brewster reflection supplies a singular/projector-type transport event. -/
def brewsterJonesTransport
    (R : FresnelReflection)
    (_hR : IsBrewsterReflection R) : JonesTransport where
  matrix := R.jones
  tag := R.tag
  kind := OpticalEventKind.brewsterReflection
  coherent := R.jones 0 1 = 0 ∧ R.jones 1 0 = 0

/-- A lossless total-internal-reflection branch supplies a phase-retarder event. -/
def losslessRetarderJonesTransport
    (R : FresnelReflection)
    (_hR : IsLosslessRetarder R) : JonesTransport where
  matrix := R.jones
  tag := R.tag
  kind := OpticalEventKind.totalInternalReflection
  coherent := R.jones 0 1 = 0 ∧ R.jones 1 0 = 0

/-- A chiral medium supplies circular-basis Cartan transport. -/
def chiralJonesTransport
    (C : CircularTransport) : JonesTransport where
  matrix := C.jones
  tag := C.tag
  kind := OpticalEventKind.chiralMedium
  coherent := C.jones 0 1 = 0 ∧ C.jones 1 0 = 0

/--
Rough or depolarizing surfaces are marked explicitly as outside the pure Jones
regime unless a concrete model supplies a coherence certificate.
-/
def depolarizingSurfaceTransport
    (M : JonesMat)
    (tag : V4Tag)
    (coherent : Prop) : JonesTransport where
  matrix := M
  tag := tag
  kind := OpticalEventKind.roughDepolarizingSurface
  coherent := coherent

end OpticalJonesV4
