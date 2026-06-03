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

@[simp] theorem id_parity : id.parity = false := rfl
@[simp] theorem id_time : id.time = false := rfl

@[simp] theorem P_parity : P.parity = true := rfl
@[simp] theorem P_time : P.time = false := rfl

@[simp] theorem T_parity : T.parity = false := rfl
@[simp] theorem T_time : T.time = true := rfl

@[simp] theorem PT_parity : PT.parity = true := rfl
@[simp] theorem PT_time : PT.time = true := rfl

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
def diagJones (a b : ℂ) : JonesMat :=
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

@[simp] theorem diagJones_apply_same_zero (a b : ℂ) :
    diagJones a b 0 0 = a := by
  simp [diagJones]

@[simp] theorem diagJones_apply_same_one (a b : ℂ) :
    diagJones a b 1 1 = b := by
  simp [diagJones]

@[simp] theorem diagJones_apply_offdiag_zero_one (a b : ℂ) :
    diagJones a b 0 1 = 0 := by
  simp [diagJones]

@[simp] theorem diagJones_apply_offdiag_one_zero (a b : ℂ) :
    diagJones a b 1 0 = 0 := by
  simp [diagJones]

@[simp] theorem sProjector_apply_same_zero :
    sProjector 0 0 = 1 := by
  simp [sProjector]

@[simp] theorem sProjector_apply_same_one :
    sProjector 1 1 = 0 := by
  simp [sProjector]

@[simp] theorem pProjector_apply_same_zero :
    pProjector 0 0 = 0 := by
  simp [pProjector]

@[simp] theorem pProjector_apply_same_one :
    pProjector 1 1 = 1 := by
  simp [pProjector]

@[simp] theorem leftCircularProjector_apply_same_zero :
    leftCircularProjector 0 0 = 1 := by
  simp [leftCircularProjector]

@[simp] theorem leftCircularProjector_apply_same_one :
    leftCircularProjector 1 1 = 0 := by
  simp [leftCircularProjector]

@[simp] theorem rightCircularProjector_apply_same_zero :
    rightCircularProjector 0 0 = 0 := by
  simp [rightCircularProjector]

@[simp] theorem rightCircularProjector_apply_same_one :
    rightCircularProjector 1 1 = 1 := by
  simp [rightCircularProjector]

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
  coherence_True : Prop

namespace JonesOpticalEvent

/-- Jones matrix of a calibrated optical event. -/
def jones (E : JonesOpticalEvent) : JonesMat :=
  diagJones E.coeff0 E.coeff1

/-- The first diagonal Jones entry is the first calibrated coefficient. -/
@[simp] theorem jones_apply_same_zero (E : JonesOpticalEvent) :
    E.jones 0 0 = E.coeff0 := by
  simp [jones, diagJones]

/-- The second diagonal Jones entry is the second calibrated coefficient. -/
@[simp] theorem jones_apply_same_one (E : JonesOpticalEvent) :
    E.jones 1 1 = E.coeff1 := by
  simp [jones, diagJones]

/-- The upper-right Jones entry vanishes for diagonal calibrated events. -/
@[simp] theorem jones_apply_offdiag_zero_one (E : JonesOpticalEvent) :
    E.jones 0 1 = 0 := by
  simp [jones, diagJones]

/-- The lower-left Jones entry vanishes for diagonal calibrated events. -/
@[simp] theorem jones_apply_offdiag_one_zero (E : JonesOpticalEvent) :
    E.jones 1 0 = 0 := by
  simp [jones, diagJones]

/-- First-channel coefficient. In `s/p`, this is `r_s`; in circular, `r_L`. -/
def firstCoeff (E : JonesOpticalEvent) : ℂ :=
  E.coeff0

/-- Second-channel coefficient. In `s/p`, this is `r_p`; in circular, `r_R`. -/
def secondCoeff (E : JonesOpticalEvent) : ℂ :=
  E.coeff1

@[simp] theorem firstCoeff_eq_coeff0 (E : JonesOpticalEvent) :
    E.firstCoeff = E.coeff0 := rfl

@[simp] theorem secondCoeff_eq_coeff1 (E : JonesOpticalEvent) :
    E.secondCoeff = E.coeff1 := rfl

end JonesOpticalEvent

/-! ## 4. Fresnel/Brewster/TIR/metal/chiral predicates -/

/--
A Brewster event in the `s/p` basis.

The `p` reflection channel vanishes while the `s` channel is nonzero.
-/
def IsBrewsterEvent (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.sp ∧
  E.kind = OpticalSurfaceKind.brewsterProjection ∧
  E.coeff1 = 0 ∧
  E.coeff0 ≠ 0

/--
A lossless retarder.

Both channels have unit magnitude. This includes idealized total internal
reflection and ideal waveplate behavior.
-/
def IsLosslessRetarder (E : JonesOpticalEvent) : Prop :=
  ‖E.coeff0‖ = 1 ∧
  ‖E.coeff1‖ = 1

/--
A diattenuating event.

The two basis channels have different magnitudes.
-/
def IsDiattenuating (E : JonesOpticalEvent) : Prop :=
  ‖E.coeff0‖ ≠ ‖E.coeff1‖

/--
A circular-birefringent event.

In the circular basis, the two handedness channels acquire unit-magnitude
phase factors.
-/
def IsCircularBirefringent (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.circular ∧
  ‖E.coeff0‖ = 1 ∧
  ‖E.coeff1‖ = 1

/--
A circular-dichroic event.

In the circular basis, left and right handedness have different attenuation.
-/
def IsCircularDichroic (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.circular ∧
  ‖E.coeff0‖ ≠ ‖E.coeff1‖

namespace JonesOpticalEvent

/-- At Brewster calibration, the second channel coefficient vanishes. -/
theorem brewster_secondCoeff_zero
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.secondCoeff = 0 := by
  exact hE.2.2.1

/-- At Brewster calibration, the first channel coefficient is nonzero. -/
theorem brewster_firstCoeff_ne_zero
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.firstCoeff ≠ 0 := by
  exact hE.2.2.2

/-- A Brewster event is in the `s/p` basis. -/
theorem brewster_basis_sp
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.basis = PolarizationBasis.sp := by
  exact hE.1

/-- A Brewster event has Brewster surface kind. -/
theorem brewster_kind
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.kind = OpticalSurfaceKind.brewsterProjection := by
  exact hE.2.1

/-- A circular-birefringent event is circular-basis. -/
theorem circularBirefringent_basis
    (E : JonesOpticalEvent)
    (hE : IsCircularBirefringent E) :
    E.basis = PolarizationBasis.circular := by
  exact hE.1

/-- The first circular-birefringent coefficient has unit norm. -/
theorem circularBirefringent_first_norm
    (E : JonesOpticalEvent)
    (hE : IsCircularBirefringent E) :
    ‖E.coeff0‖ = 1 := by
  exact hE.2.1

/-- The second circular-birefringent coefficient has unit norm. -/
theorem circularBirefringent_second_norm
    (E : JonesOpticalEvent)
    (hE : IsCircularBirefringent E) :
    ‖E.coeff1‖ = 1 := by
  exact hE.2.2

/-- A circular-dichroic event is circular-basis. -/
theorem circularDichroic_basis
    (E : JonesOpticalEvent)
    (hE : IsCircularDichroic E) :
    E.basis = PolarizationBasis.circular := by
  exact hE.1

/-- A circular-dichroic event is diattenuating. -/
theorem circularDichroic_isDiattenuating
    (E : JonesOpticalEvent)
    (hE : IsCircularDichroic E) :
    IsDiattenuating E := by
  exact hE.2

/-- A circular-birefringent event is lossless. -/
theorem circularBirefringent_isLossless
    (E : JonesOpticalEvent)
    (hE : IsCircularBirefringent E) :
    IsLosslessRetarder E := by
  exact ⟨hE.2.1, hE.2.2⟩

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
  tag_True : Prop
  /--
  Optical channel law.

  This is where a concrete module may say, for example, that a metal mirror is
  represented by a PT-tagged lossy retarder, or that Brewster reflection is a
  rank-collapse boundary event.
  -/
  channel_True : Prop

/-- A Brewster calibration packages an event with its rank-collapse proof. -/
structure BrewsterCalibration where
  event : JonesOpticalEvent
  is_brewster : IsBrewsterEvent event

/-- A total-internal-reflection calibration packages a lossless retarder event. -/
structure TIRCalibration where
  event : JonesOpticalEvent
  is_lossless : IsLosslessRetarder event
  tir_True : Prop

/-- A metal-mirror calibration packages a possibly lossy complex retarder. -/
structure MetalMirrorCalibration where
  event : JonesOpticalEvent
  is_metal : event.kind = OpticalSurfaceKind.metalMirror
  metal_True : Prop

/-- A chiral calibration packages a circular-basis event. -/
structure ChiralCalibration where
  event : JonesOpticalEvent
  circular_basis : event.basis = PolarizationBasis.circular
  chiral_kind : event.kind = OpticalSurfaceKind.chiralMedium
  chiral_True : Prop

/-- A metasurface calibration packages a structured anisotropic interface. -/
structure MetasurfaceCalibration where
  event : JonesOpticalEvent
  is_metasurface : event.kind = OpticalSurfaceKind.metasurface
  metasurface_True : Prop

namespace BrewsterCalibration

@[simp] theorem event_basis_sp (B : BrewsterCalibration) :
    B.event.basis = PolarizationBasis.sp := by
  exact B.is_brewster.1

@[simp] theorem event_kind_brewster (B : BrewsterCalibration) :
    B.event.kind = OpticalSurfaceKind.brewsterProjection := by
  exact B.is_brewster.2.1

@[simp] theorem secondCoeff_zero (B : BrewsterCalibration) :
    B.event.secondCoeff = 0 := by
  exact JonesOpticalEvent.brewster_secondCoeff_zero B.event B.is_brewster

theorem firstCoeff_ne_zero (B : BrewsterCalibration) :
    B.event.firstCoeff ≠ 0 := by
  exact JonesOpticalEvent.brewster_firstCoeff_ne_zero B.event B.is_brewster

@[simp] theorem jones_p_channel_zero (B : BrewsterCalibration) :
    B.event.jones 1 1 = 0 := by
  rw [JonesOpticalEvent.jones_apply_same_one]
  exact B.secondCoeff_zero

end BrewsterCalibration

namespace TIRCalibration

theorem coeff0_norm_one (T : TIRCalibration) :
    ‖T.event.coeff0‖ = 1 := by
  exact T.is_lossless.1

theorem coeff1_norm_one (T : TIRCalibration) :
    ‖T.event.coeff1‖ = 1 := by
  exact T.is_lossless.2

end TIRCalibration

namespace MetalMirrorCalibration

@[simp] theorem event_kind (M : MetalMirrorCalibration) :
    M.event.kind = OpticalSurfaceKind.metalMirror := by
  exact M.is_metal

end MetalMirrorCalibration

namespace ChiralCalibration

@[simp] theorem event_basis (C : ChiralCalibration) :
    C.event.basis = PolarizationBasis.circular := by
  exact C.circular_basis

@[simp] theorem event_kind (C : ChiralCalibration) :
    C.event.kind = OpticalSurfaceKind.chiralMedium := by
  exact C.chiral_kind

end ChiralCalibration

namespace MetasurfaceCalibration

@[simp] theorem event_kind (M : MetasurfaceCalibration) :
    M.event.kind = OpticalSurfaceKind.metasurface := by
  exact M.is_metasurface

end MetasurfaceCalibration

/-! ## 6. Elementary calibrated constructors -/

/-- Abstract coherent event constructor. -/
def mkAbstractEvent
    (basis : PolarizationBasis)
    (coeff0 coeff1 : ℂ)
    (tag : V4Tag)
    (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := basis
    kind := OpticalSurfaceKind.abstract
    coeff0 := coeff0
    coeff1 := coeff1
    tag := tag
    coherence_True := coherence_True }

/-- Brewster event constructor from channel data. -/
def mkBrewsterEvent
    (rs : ℂ)
    (_hrs : rs ≠ 0)
    (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := PolarizationBasis.sp
    kind := OpticalSurfaceKind.brewsterProjection
    coeff0 := rs
    coeff1 := 0
    tag := V4Tag.P
    coherence_True := coherence_True }

@[simp] theorem mkBrewsterEvent_isBrewster
    (rs : ℂ)
    (hrs : rs ≠ 0)
    (coherence_True : Prop) :
    IsBrewsterEvent (mkBrewsterEvent rs hrs coherence_True) := by
  simp [mkBrewsterEvent, IsBrewsterEvent, hrs]

/-- Brewster calibration constructor from nonzero `s` coefficient. -/
def mkBrewsterCalibration
    (rs : ℂ)
    (hrs : rs ≠ 0)
    (coherence_True : Prop) : BrewsterCalibration :=
  { event := mkBrewsterEvent rs hrs coherence_True
    is_brewster := mkBrewsterEvent_isBrewster rs hrs coherence_True }

/-- Total-internal-reflection event constructor from unit-norm coefficients. -/
def mkTIREvent
    (r0 r1 : ℂ)
    (_h0 : ‖r0‖ = 1)
    (_h1 : ‖r1‖ = 1)
    (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := PolarizationBasis.sp
    kind := OpticalSurfaceKind.totalInternalReflection
    coeff0 := r0
    coeff1 := r1
    tag := V4Tag.T
    coherence_True := coherence_True }

@[simp] theorem mkTIREvent_isLossless
    (r0 r1 : ℂ)
    (h0 : ‖r0‖ = 1)
    (h1 : ‖r1‖ = 1)
    (coherence_True : Prop) :
    IsLosslessRetarder (mkTIREvent r0 r1 h0 h1 coherence_True) := by
  simp [mkTIREvent, IsLosslessRetarder, h0, h1]

/-- Total-internal-reflection calibration constructor. -/
def mkTIRCalibration
    (r0 r1 : ℂ)
    (h0 : ‖r0‖ = 1)
    (h1 : ‖r1‖ = 1)
    (coherence_True : Prop)
    (tir_True : Prop) : TIRCalibration :=
  { event := mkTIREvent r0 r1 h0 h1 coherence_True
    is_lossless := mkTIREvent_isLossless r0 r1 h0 h1 coherence_True
    tir_True := tir_True }

/-- Circular-birefringent chiral event constructor. -/
def mkCircularBirefringentEvent
    (rL rR : ℂ)
    (_hL : ‖rL‖ = 1)
    (_hR : ‖rR‖ = 1)
    (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := PolarizationBasis.circular
    kind := OpticalSurfaceKind.chiralMedium
    coeff0 := rL
    coeff1 := rR
    tag := V4Tag.id
    coherence_True := coherence_True }

@[simp] theorem mkCircularBirefringentEvent_isCircularBirefringent
    (rL rR : ℂ)
    (hL : ‖rL‖ = 1)
    (hR : ‖rR‖ = 1)
    (coherence_True : Prop) :
    IsCircularBirefringent
      (mkCircularBirefringentEvent rL rR hL hR coherence_True) := by
  simp [mkCircularBirefringentEvent, IsCircularBirefringent, hL, hR]

/-- Circular-dichroic chiral event constructor. -/
def mkCircularDichroicEvent
    (rL rR : ℂ)
    (_hLR : ‖rL‖ ≠ ‖rR‖)
    (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := PolarizationBasis.circular
    kind := OpticalSurfaceKind.chiralMedium
    coeff0 := rL
    coeff1 := rR
    tag := V4Tag.PT
    coherence_True := coherence_True }

@[simp] theorem mkCircularDichroicEvent_isCircularDichroic
    (rL rR : ℂ)
    (hLR : ‖rL‖ ≠ ‖rR‖)
    (coherence_True : Prop) :
    IsCircularDichroic
      (mkCircularDichroicEvent rL rR hLR coherence_True) := by
  simp [mkCircularDichroicEvent, IsCircularDichroic, hLR]

/-! ## 7. Matrix-level diagonal facts -/

namespace JonesOpticalEvent

theorem jones_eq_coeff_projector_sum (E : JonesOpticalEvent) :
    E.jones =
      E.coeff0 • sProjector + E.coeff1 • pProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jones, diagJones, sProjector, pProjector]

theorem brewster_jones_eq_firstCoeff_sProjector
    (E : JonesOpticalEvent)
    (hE : IsBrewsterEvent E) :
    E.jones = E.firstCoeff • sProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jones, diagJones, sProjector, firstCoeff, hE.2.2.1]

theorem lossless_coeff0_norm_one
    (E : JonesOpticalEvent)
    (hE : IsLosslessRetarder E) :
    ‖E.coeff0‖ = 1 := by
  exact hE.1

theorem lossless_coeff1_norm_one
    (E : JonesOpticalEvent)
    (hE : IsLosslessRetarder E) :
    ‖E.coeff1‖ = 1 := by
  exact hE.2

end JonesOpticalEvent

end InfoGeometry.OperatorAlgebra.JonesCalibration
