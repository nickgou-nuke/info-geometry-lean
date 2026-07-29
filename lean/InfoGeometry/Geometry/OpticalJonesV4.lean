/-
InfoGeometry/Geometry/OpticalJonesV4.lean

Operatorial Jones calculus with V4 orientation tags.

The Fresnel/Jones coefficients are continuous optical data.  The V4 tag records
the discrete orientation/parity/time-reversal bookkeeping of the event.
-/

import Mathlib.Tactic
import InfoGeometry.Geometry.OperatorialJonesConnection
import InfoGeometry.Geometry.KleinFourTag
import InfoGeometry.Optics.FiniteJonesModel

noncomputable section

namespace InfoGeometry.Geometry.OpticalJonesV4

/-! ## 1. V4 orientation tags -/

/-- Canonical Klein-four parity/time orientation tag. -/
abbrev V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.Tag

namespace V4Tag

/-- Identity sector. -/
def id : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.id

/-- Parity/spatial reflection sector. -/
def P : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.P

/-- Time/propagation-reversal sector. -/
def T : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.T

/-- Combined PT sector. -/
def PT : V4Tag :=
  InfoGeometry.Geometry.KleinFourTag.PT

end V4Tag

/-! ## 2. Jones matrices -/

/-- Two-component Jones vector. -/
abbrev JonesVec :=
  Fin 2 → ℂ

/-- Two-by-two Jones matrix. -/
abbrev JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.JonesMat

/--
Diagonal Jones matrix.

The convention is index `0 = s` or `L`, index `1 = p` or `R`, depending on
the chosen basis.
-/
def diagJones
    (a b : ℂ) : JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.diagJones a b

/-- The `s`-sector projector in the Fresnel `s/p` basis. -/
def sProjector : JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.sProjector

/-- The `p`-sector projector in the Fresnel `s/p` basis. -/
def pProjector : JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.pProjector

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

/-- Independent data determining a scaled-projector event.

The realized matrix is derived rather than stored together with an equality
certificate.
-/
abbrev ScaledProjectorEvent :=
  ℂ × JonesMat

namespace ScaledProjectorEvent

/-- Scalar optical coefficient. -/
def scale (E : ScaledProjectorEvent) : ℂ :=
  E.1

/-- Projector channel selected by the event. -/
def projector (E : ScaledProjectorEvent) : JonesMat :=
  E.2

/-- Matrix canonically realized by the event. -/
def matrix (E : ScaledProjectorEvent) : JonesMat :=
  E.scale • E.projector

/-- The realized matrix is definitionally the scaled projector. -/
@[simp]
theorem matrix_eq_scaled_projector (E : ScaledProjectorEvent) :
    E.matrix = E.scale • E.projector :=
  rfl

end ScaledProjectorEvent

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

This packages a Jones matrix with its discrete V4 orientation tag.  Coherence,
complete positivity, and noncommutative transport laws belong to their
operator-algebraic owners and are not represented by free proposition fields.
-/
structure JonesTransport where
  /-- Continuous Jones/Fresnel operator. -/
  matrix : JonesMat

  /-- Discrete orientation/PT/parity bookkeeping. -/
  tag : V4Tag

  /-- Optical event type. -/
  kind : OpticalEventKind

/-- A Fresnel reflection supplies a diagonal `s/p` Jones transport. -/
def fresnelJonesTransport
    (R : FresnelReflection) : JonesTransport where
  matrix := R.jones
  tag := R.tag
  kind := OpticalEventKind.dielectricReflection

/-- A Brewster reflection supplies a singular/projector-type transport event. -/
def brewsterJonesTransport
    (R : FresnelReflection)
    (_hR : IsBrewsterReflection R) : JonesTransport where
  matrix := R.jones
  tag := R.tag
  kind := OpticalEventKind.brewsterReflection

/-- A lossless total-internal-reflection branch supplies a phase-retarder event. -/
def losslessRetarderJonesTransport
    (R : FresnelReflection)
    (_hR : IsLosslessRetarder R) : JonesTransport where
  matrix := R.jones
  tag := R.tag
  kind := OpticalEventKind.totalInternalReflection

/-- A chiral medium supplies circular-basis Cartan transport. -/
def chiralJonesTransport
    (C : CircularTransport) : JonesTransport where
  matrix := C.jones
  tag := C.tag
  kind := OpticalEventKind.chiralMedium

/--
Rough or depolarizing surfaces are marked explicitly as outside the pure Jones
regime unless a concrete model supplies a coherence certificate.
-/
def depolarizingSurfaceTransport
    (M : JonesMat)
    (tag : V4Tag) : JonesTransport where
  matrix := M
  tag := tag
  kind := OpticalEventKind.roughDepolarizingSurface

/-! ## 6. Noncommutative operatorial realization -/

open InfoGeometry.Geometry.OperatorialJonesConnection

/--
An operatorial Jones transport realizes the optical matrix event when its
underlying unit is exactly the event matrix.

This is an explicit bridge relation, not a coherence marker.
-/
def JonesTransportRealizesOperatorial
    (J : JonesTransport)
    (C : ChiralCartanProjectors JonesMat)
    (T : OperatorialJonesTransport JonesMat C) : Prop :=
  T.U.val = J.matrix

/--
Genuine noncommutative replacement for the former unconstrained
`JonesTransport.coherent : Prop` field.

A Jones event is coherent precisely when its matrix is realized by an
invertible operatorial transport whose conjugation action preserves algebraic
projectors and whose action on the chiral Cartan axis is controlled.
-/
def JonesTransport.coherent (J : JonesTransport) : Prop :=
  ∃ (C : ChiralCartanProjectors JonesMat)
      (T : OperatorialJonesTransport JonesMat C),
    JonesTransportRealizesOperatorial J C T

/-- Coherence is exactly existence of an operatorial Jones realization. -/
theorem JonesTransport.coherent_iff_exists_operatorial
    (J : JonesTransport) :
    J.coherent ↔
      ∃ (C : ChiralCartanProjectors JonesMat)
          (T : OperatorialJonesTransport JonesMat C),
        JonesTransportRealizesOperatorial J C T :=
  Iff.rfl

/--
Every realized operatorial Jones event has an invertible representative whose
noncommutative conjugation action preserves algebraic projectors.
-/
theorem operatorial_realization_preserves_projector
    (J : JonesTransport)
    (C : ChiralCartanProjectors JonesMat)
    (T : OperatorialJonesTransport JonesMat C)
    (hRealizes : JonesTransportRealizesOperatorial J C T)
    {P : JonesMat}
    (hP : IsProjector P) :
    ∃ U : Units JonesMat,
      U.val = J.matrix ∧ IsProjector (conjugationAction U P) :=
  ⟨T.U, hRealizes, T.maps_projector hP⟩

/--
Historical projector-preservation API, recovered as a direct corollary of the
operatorial conjugation owner.  The realization hypothesis identifies the
optical event with `T`; projector preservation itself is the native theorem
carried by that noncommutative transport.
-/
theorem maps_projector_of_operatorial_realization
    (J : JonesTransport)
    (C : ChiralCartanProjectors JonesMat)
    (T : OperatorialJonesTransport JonesMat C)
    (_hRealizes : JonesTransportRealizesOperatorial J C T)
    {P : JonesMat}
    (hP : IsProjector P) :
    IsProjector (conjugationAction T.U P) :=
  T.maps_projector hP

/-- A realized Jones matrix genuinely preserves or reverses the Cartan axis. -/
theorem operatorial_realization_cartan_behavior
    (J : JonesTransport)
    (C : ChiralCartanProjectors JonesMat)
    (T : OperatorialJonesTransport JonesMat C)
    (hRealizes : JonesTransportRealizesOperatorial J C T) :
    PreservesCartanAxis C.chi J.matrix ∨
      ReversesCartanAxis C.chi J.matrix := by
  have hU : T.U.val = J.matrix := hRealizes
  rw [← hU]
  exact T.cartan_behavior

end InfoGeometry.Geometry.OpticalJonesV4
