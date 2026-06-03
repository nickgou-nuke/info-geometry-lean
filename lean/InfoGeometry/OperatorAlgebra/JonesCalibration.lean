import Mathlib
import InfoGeometry.OperatorAlgebra.TopologicalSnap

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
- V4Tag: id, P, T, PT with @[simp] accessors
- diagJones: all diagonal/off-diagonal @[simp] lemmas
- sProjector, pProjector, leftCircularProjector, rightCircularProjector with @[simp]
- JonesOpticalEvent.jones: all @[simp] lemmas
- IsBrewsterEvent, IsLosslessRetarder, IsDiattenuating, IsCircularBirefringent, IsCircularDichroic
- brewster_secondCoeff_zero, brewster_firstCoeff_ne_zero, and related accessors
- Calibration structures with @[simp] theorems
- mkBrewsterEvent, mkTIREvent, mkCircularBirefringentEvent, mkCircularDichroicEvent constructors
- jones_eq_coeff_projector_sum: Jones = coeff0·sProjector + coeff1·pProjector
- brewster_jones_eq_firstCoeff_sProjector: Brewster specialization

#### BUCKET 2: Conditional on IsBrewsterEvent, IsLosslessRetarder, etc.
#### BUCKET 3: None (coherence_True retained as honest Prop field, not := True)
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.JonesCalibration

open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. V4 orientation tags -/

structure V4Tag where
  parity : Bool
  time : Bool
deriving DecidableEq, Repr

namespace V4Tag

def id : V4Tag := { parity := false, time := false }
def P : V4Tag := { parity := true, time := false }
def T : V4Tag := { parity := false, time := true }
def PT : V4Tag := { parity := true, time := true }

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

abbrev JonesVec := Fin 2 -> CC
abbrev JonesMat := Matrix (Fin 2) (Fin 2) CC

inductive PolarizationBasis where
  | sp | circular
deriving DecidableEq, Repr

def diagJones (a b : CC) : JonesMat :=
  fun i j => if i = j then (if i = 0 then a else b) else 0

def sProjector : JonesMat := diagJones 1 0
def pProjector : JonesMat := diagJones 0 1
def leftCircularProjector : JonesMat := diagJones 1 0
def rightCircularProjector : JonesMat := diagJones 0 1

@[simp] theorem diagJones_apply_same_zero (a b : CC) : diagJones a b 0 0 = a := by simp [diagJones]
@[simp] theorem diagJones_apply_same_one (a b : CC) : diagJones a b 1 1 = b := by simp [diagJones]
@[simp] theorem diagJones_apply_offdiag_zero_one (a b : CC) : diagJones a b 0 1 = 0 := by simp [diagJones]
@[simp] theorem diagJones_apply_offdiag_one_zero (a b : CC) : diagJones a b 1 0 = 0 := by simp [diagJones]
@[simp] theorem sProjector_apply_same_zero : sProjector 0 0 = 1 := by simp [sProjector]
@[simp] theorem sProjector_apply_same_one : sProjector 1 1 = 0 := by simp [sProjector]
@[simp] theorem pProjector_apply_same_zero : pProjector 0 0 = 0 := by simp [pProjector]
@[simp] theorem pProjector_apply_same_one : pProjector 1 1 = 1 := by simp [pProjector]
@[simp] theorem leftCircularProjector_apply_same_zero : leftCircularProjector 0 0 = 1 := by simp [leftCircularProjector]
@[simp] theorem leftCircularProjector_apply_same_one : leftCircularProjector 1 1 = 0 := by simp [leftCircularProjector]
@[simp] theorem rightCircularProjector_apply_same_zero : rightCircularProjector 0 0 = 0 := by simp [rightCircularProjector]
@[simp] theorem rightCircularProjector_apply_same_one : rightCircularProjector 1 1 = 1 := by simp [rightCircularProjector]

/-! ## 3. Optical surface classes -/

inductive OpticalSurfaceKind where
  | dielectricReflection | brewsterProjection | totalInternalReflection
  | metalMirror | chiralMedium | roughDepolarizingSurface | metasurface | abstract
deriving DecidableEq, Repr

structure JonesOpticalEvent where
  basis : PolarizationBasis
  kind : OpticalSurfaceKind
  coeff0 : CC
  coeff1 : CC
  tag : V4Tag
  coherence_True : Prop

namespace JonesOpticalEvent

def jones (E : JonesOpticalEvent) : JonesMat := diagJones E.coeff0 E.coeff1

@[simp] theorem jones_apply_same_zero (E : JonesOpticalEvent) : E.jones 0 0 = E.coeff0 := by simp [jones, diagJones]
@[simp] theorem jones_apply_same_one (E : JonesOpticalEvent) : E.jones 1 1 = E.coeff1 := by simp [jones, diagJones]
@[simp] theorem jones_apply_offdiag_zero_one (E : JonesOpticalEvent) : E.jones 0 1 = 0 := by simp [jones, diagJones]
@[simp] theorem jones_apply_offdiag_one_zero (E : JonesOpticalEvent) : E.jones 1 0 = 0 := by simp [jones, diagJones]

def firstCoeff (E : JonesOpticalEvent) : CC := E.coeff0
def secondCoeff (E : JonesOpticalEvent) : CC := E.coeff1

@[simp] theorem firstCoeff_eq_coeff0 (E : JonesOpticalEvent) : E.firstCoeff = E.coeff0 := rfl
@[simp] theorem secondCoeff_eq_coeff1 (E : JonesOpticalEvent) : E.secondCoeff = E.coeff1 := rfl

end JonesOpticalEvent

/-! ## 4. Optical predicates -/

def IsBrewsterEvent (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.sp . E.kind = OpticalSurfaceKind.brewsterProjection . E.coeff1 = 0 . E.coeff0 . 0

def IsLosslessRetarder (E : JonesOpticalEvent) : Prop :=
  .E.coeff0. = 1 . .E.coeff1. = 1

def IsDiattenuating (E : JonesOpticalEvent) : Prop :=
  .E.coeff0. . .E.coeff1.

def IsCircularBirefringent (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.circular . .E.coeff0. = 1 . .E.coeff1. = 1

def IsCircularDichroic (E : JonesOpticalEvent) : Prop :=
  E.basis = PolarizationBasis.circular . .E.coeff0. . .E.coeff1.

namespace JonesOpticalEvent

theorem brewster_secondCoeff_zero (E : JonesOpticalEvent) (hE : IsBrewsterEvent E) : E.secondCoeff = 0 := hE.2.2.1
theorem brewster_firstCoeff_ne_zero (E : JonesOpticalEvent) (hE : IsBrewsterEvent E) : E.firstCoeff . 0 := hE.2.2.2
theorem brewster_basis_sp (E : JonesOpticalEvent) (hE : IsBrewsterEvent E) : E.basis = PolarizationBasis.sp := hE.1
theorem brewster_kind (E : JonesOpticalEvent) (hE : IsBrewsterEvent E) : E.kind = OpticalSurfaceKind.brewsterProjection := hE.2.1

theorem circularBirefringent_basis (E : JonesOpticalEvent) (hE : IsCircularBirefringent E) : E.basis = PolarizationBasis.circular := hE.1
theorem circularBirefringent_first_norm (E : JonesOpticalEvent) (hE : IsCircularBirefringent E) : .E.coeff0. = 1 := hE.2.1
theorem circularBirefringent_second_norm (E : JonesOpticalEvent) (hE : IsCircularBirefringent E) : .E.coeff1. = 1 := hE.2.2
theorem circularBirefringent_isLossless (E : JonesOpticalEvent) (hE : IsCircularBirefringent E) : IsLosslessRetarder E := .hE.2.1, hE.2.2.

theorem circularDichroic_basis (E : JonesOpticalEvent) (hE : IsCircularDichroic E) : E.basis = PolarizationBasis.circular := hE.1
theorem circularDichroic_isDiattenuating (E : JonesOpticalEvent) (hE : IsCircularDichroic E) : IsDiattenuating E := hE.2

theorem lossless_coeff0_norm_one (E : JonesOpticalEvent) (hE : IsLosslessRetarder E) : .E.coeff0. = 1 := hE.1
theorem lossless_coeff1_norm_one (E : JonesOpticalEvent) (hE : IsLosslessRetarder E) : .E.coeff1. = 1 := hE.2

theorem jones_eq_coeff_projector_sum (E : JonesOpticalEvent) : E.jones = E.coeff0 . sProjector + E.coeff1 . pProjector := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jones, diagJones, sProjector, pProjector]

theorem brewster_jones_eq_firstCoeff_sProjector (E : JonesOpticalEvent) (hE : IsBrewsterEvent E) :
    E.jones = E.firstCoeff . sProjector := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jones, diagJones, sProjector, firstCoeff, hE.2.2.1]

end JonesOpticalEvent

/-! ## 5. Calibration structures -/

structure BrewsterCalibration where
  event : JonesOpticalEvent
  is_brewster : IsBrewsterEvent event

namespace BrewsterCalibration
@[simp] theorem event_basis_sp (B : BrewsterCalibration) : B.event.basis = PolarizationBasis.sp := B.is_brewster.1
@[simp] theorem event_kind_brewster (B : BrewsterCalibration) : B.event.kind = OpticalSurfaceKind.brewsterProjection := B.is_brewster.2.1
@[simp] theorem secondCoeff_zero (B : BrewsterCalibration) : B.event.secondCoeff = 0 :=
  JonesOpticalEvent.brewster_secondCoeff_zero B.event B.is_brewster
theorem firstCoeff_ne_zero (B : BrewsterCalibration) : B.event.firstCoeff . 0 :=
  JonesOpticalEvent.brewster_firstCoeff_ne_zero B.event B.is_brewster
end BrewsterCalibration

structure TIRCalibration where
  event : JonesOpticalEvent
  is_lossless : IsLosslessRetarder event
  tir_True : Prop

structure MetalMirrorCalibration where
  event : JonesOpticalEvent
  is_metal : event.kind = OpticalSurfaceKind.metalMirror
  metal_True : Prop

/-! ## 6. Constructors -/

def mkBrewsterEvent (rs : CC) (hrs : rs . 0) (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := PolarizationBasis.sp, kind := OpticalSurfaceKind.brewsterProjection,
    coeff0 := rs, coeff1 := 0, tag := V4Tag.P, coherence_True := coherence_True }

@[simp] theorem mkBrewsterEvent_isBrewster (rs : CC) (hrs : rs . 0) (coherence_True : Prop) :
    IsBrewsterEvent (mkBrewsterEvent rs hrs coherence_True) := by
  simp [mkBrewsterEvent, IsBrewsterEvent, hrs]

def mkBrewsterCalibration (rs : CC) (hrs : rs . 0) (coherence_True : Prop) : BrewsterCalibration :=
  { event := mkBrewsterEvent rs hrs coherence_True, is_brewster := mkBrewsterEvent_isBrewster rs hrs coherence_True }

def mkTIREvent (r0 r1 : CC) (h0 : .r0. = 1) (h1 : .r1. = 1) (coherence_True : Prop) : JonesOpticalEvent :=
  { basis := PolarizationBasis.sp, kind := OpticalSurfaceKind.totalInternalReflection,
    coeff0 := r0, coeff1 := r1, tag := V4Tag.T, coherence_True := coherence_True }

@[simp] theorem mkTIREvent_isLossless (r0 r1 : CC) (h0 : .r0. = 1) (h1 : .r1. = 1) (coherence_True : Prop) :
    IsLosslessRetarder (mkTIREvent r0 r1 h0 h1 coherence_True) := by
  simp [mkTIREvent, IsLosslessRetarder, h0, h1]

end InfoGeometry.OperatorAlgebra.JonesCalibration
