/-
InfoGeometry/OperatorAlgebra/HelicalTimeStinespring.lean

Helical modular time, spectral divisor charge, and Stinespring hidden-sector
bookkeeping.

The key distinction:

* zeros of a spectral function are divisor locations;
* charges are integer monodromy/multiplicity/winding readouts attached to those
  locations;
* Stinespring dilation routes visible loss into a hidden sector, and a
  calibration may say that the hidden sector carries the helical sheet charge.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.HelicalTimeStinespring

open InfoGeometry.OperatorAlgebra.StinespringDilation

/-! ## 1. Helical time -/

/--
A helical time structure on a state space.

`angle` is the local circular phase.
`sheet` is the integer timesheet/winding index.
`flow` is the modular/helical flow.

The key law says that one full turn advances the sheet by one.
-/
structure HelicalTimeDatum
    (State : Type*) where
  angle : State → ℝ
  sheet : State → ℤ
  flow : ℝ → State → State
  flow_zero :
    ∀ x : State, flow 0 x = x
  flow_add :
    ∀ s t x, flow (s + t) x = flow s (flow t x)
  sheet_after_full_turn :
    ∀ x : State,
      sheet (flow (2 * Real.pi) x) = sheet x + 1

namespace HelicalTimeDatum

variable {State : Type*}
variable (H : HelicalTimeDatum State)

@[simp]
theorem flow_zero_apply
    (x : State) :
    H.flow 0 x = x :=
  H.flow_zero x

theorem flow_add_apply
    (s t : ℝ)
    (x : State) :
    H.flow (s + t) x = H.flow s (H.flow t x) :=
  H.flow_add s t x

theorem one_turn_increments_sheet
    (x : State) :
    H.sheet (H.flow (2 * Real.pi) x) = H.sheet x + 1 :=
  H.sheet_after_full_turn x

end HelicalTimeDatum

/-! ## 2. Spectral divisors and winding charge -/

/--
A spectral divisor datum for a complex spectral function.

`L` is the spectral/scattering/L-function-like readout.
`zeroLocus` records divisor locations.
`multiplicity` records integer multiplicity at a point.
`chargeOf` records a contour/region count. A concrete module may implement it
using the argument principle or a winding-number integral.
-/
structure SpectralDivisorDatum where
  L : ℂ → ℂ
  zeroLocus : Set ℂ
  multiplicity : ℂ → ℤ
  chargeOf : Set ℂ → ℤ
  zeroLocus_spec :
    ∀ s : ℂ, s ∈ zeroLocus ↔ L s = 0

/-- A point is a spectral zero of the divisor datum. -/
def IsSpectralZero
    (D : SpectralDivisorDatum)
    (s : ℂ) : Prop :=
  s ∈ D.zeroLocus

namespace SpectralDivisorDatum

variable (D : SpectralDivisorDatum)

theorem isSpectralZero_iff
    (s : ℂ) :
    IsSpectralZero D s ↔ D.L s = 0 := by
  unfold IsSpectralZero
  exact D.zeroLocus_spec s

/-- The divisor locations are exactly the zeroes of the spectral function. -/
theorem divisor
    (s : ℂ) :
    s ∈ D.zeroLocus ↔ D.L s = 0 :=
  D.zeroLocus_spec s

end SpectralDivisorDatum

/--
A helical spectral charge calibration.

This connects sheet/winding data to a spectral divisor count.
-/
structure HelicalSpectralChargeCalibration
    (State : Type*)
    (H : HelicalTimeDatum State)
    (D : SpectralDivisorDatum) where
  /-- Spectral region/contour assigned to a state. -/
  spectralRegion : State → Set ℂ
  /-- The helical sheet index equals the divisor charge of the region. -/
  sheet_eq_divisor_charge :
    ∀ x : State,
      H.sheet x = D.chargeOf (spectralRegion x)

namespace HelicalSpectralChargeCalibration

variable
    {State : Type*}
    {H : HelicalTimeDatum State}
    {D : SpectralDivisorDatum}

variable (C : HelicalSpectralChargeCalibration State H D)

theorem sheet_eq_charge
    (x : State) :
    H.sheet x = D.chargeOf (C.spectralRegion x) :=
  C.sheet_eq_divisor_charge x

/-- The helical sheet readout is calibrated by the divisor charge. -/
theorem monodromy
    (x : State) :
    H.sheet x = D.chargeOf (C.spectralRegion x) :=
  C.sheet_eq_divisor_charge x

end HelicalSpectralChargeCalibration

/-! ## 3. Projection packet over timesheets -/

/--
A projection packet over helical sheets.

This is the formal version of a state distributed over multiple timesheets.
-/
structure ProjectionPacket
    (Proj : Type*) where
  weight : ℤ → ℝ
  projector : ℤ → Proj
  finiteSupport : Prop
  normalized : Prop

/-- A readout of the packet on a selected visible sheet. -/
def visibleSheetReadout
    {Proj : Type*}
    (P : ProjectionPacket Proj)
    (N : ℤ) : Proj :=
  P.projector N

/-! ## 4. Stinespring hidden sector carries helical charge -/

/--
A calibration saying that Stinespring hidden flow carries helical sheet charge.

This is the precise bridge from dissipative visible loss to helical hidden
bookkeeping.
-/
structure HelicalStinespringCalibration
    (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Helical time on the visible system. -/
  visibleHelix : HelicalTimeDatum Sys
  /-- Helical time on the hidden/commutant sector. -/
  hiddenHelix : HelicalTimeDatum Comm
  /-- Hidden flow carries the visible sheet charge. -/
  hidden_sheet_eq_visible_sheet :
    ∀ x : Sys,
      hiddenHelix.sheet (D.hiddenFlow x) =
        visibleHelix.sheet x

namespace HelicalStinespringCalibration

variable
    {Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : HelicalStinespringCalibration Sys Comm C D)

/--
The hidden Stinespring sector carries the same helical sheet charge as the
visible input.
-/
theorem hidden_sheet_eq_visible_sheet_apply
    (x : Sys) :
    K.hiddenHelix.sheet (D.hiddenFlow x) =
      K.visibleHelix.sheet x :=
  K.hidden_sheet_eq_visible_sheet x

/-- One-turn visible flow corresponds to sheet bookkeeping in the hidden sector. -/
theorem one_turn_hidden_charge
    (x : Sys) :
    K.hiddenHelix.sheet (D.hiddenFlow (K.visibleHelix.flow (2 * Real.pi) x)) =
      K.visibleHelix.sheet x + 1 := by
  rw [K.hidden_sheet_eq_visible_sheet_apply]
  exact K.visibleHelix.one_turn_increments_sheet x

/--
The visible deficit is still the recovered hidden flow; the helical calibration
adds sheet bookkeeping but does not replace Stinespring conservation.
-/
theorem visible_deficit_eq_recovered_hidden
    (x : Sys) :
    C.ideal x - C.actual x =
      D.recoverHidden (D.hiddenFlow x) :=
  D.ideal_sub_actual_eq_recovered_hidden x

end HelicalStinespringCalibration

/-! ## 5. Riemann/L-function divisor branch -/

/--
A Riemann/L-function branch calibration.

This does not identify zeroes with charges. It says that the divisor of the
chosen spectral function supplies integer winding/sheet charges.
-/
structure LFunctionHelicalBranch
    (State : Type*) where
  helix : HelicalTimeDatum State
  divisor : SpectralDivisorDatum
  calibration :
    HelicalSpectralChargeCalibration State helix divisor
  /--
  Certificate that the spectral function is the intended zeta/L/scattering
  determinant for this model.
  -/
  spectral_function_calibrated : Prop

namespace LFunctionHelicalBranch

variable {State : Type*}
variable (B : LFunctionHelicalBranch State)

/-- The helical sheet of a state is the divisor charge of its spectral region. -/
theorem sheet_eq_divisor_charge
    (x : State) :
    B.helix.sheet x =
      B.divisor.chargeOf (B.calibration.spectralRegion x) :=
  B.calibration.sheet_eq_charge x

end LFunctionHelicalBranch

/-! ## 6. Owner target -/

/--
Owner target for helical Stinespring bookkeeping.

Once a helical Stinespring calibration is supplied, the hidden sector carries
the visible sheet charge.
-/
@[owner_target_tag]
def HelicalStinespringOwnerTarget : Prop :=
  ∀ (Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm],
  ∀ C : DissipativeChannel Sys,
  ∀ D : StinespringTomitaDilation Sys Comm C,
  ∀ K : HelicalStinespringCalibration Sys Comm C D,
  ∀ x : Sys,
    K.hiddenHelix.sheet (D.hiddenFlow x) =
      K.visibleHelix.sheet x

/-- The owner target follows from the supplied calibration. -/
theorem helicalStinespringOwnerTarget :
    HelicalStinespringOwnerTarget := by
  intro Sys Comm _ _ _ _ C D K x
  exact K.hidden_sheet_eq_visible_sheet_apply x

end InfoGeometry.OperatorAlgebra.HelicalTimeStinespring
