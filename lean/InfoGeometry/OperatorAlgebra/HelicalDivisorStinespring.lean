/-
InfoGeometry/OperatorAlgebra/HelicalDivisorStinespring.lean

Helical modular sheets, spectral divisors, and Stinespring hidden-sector
accounting.

Divisor points are not themselves the charge.  The charge is the integer
winding/multiplicity/monodromy readout around a divisor.

This module is generic.  Riemann/L-function zeroes, material resonances, and
scattering determinant zeroes are later instantiations supplied by calibration.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TopologicalSnap
import InfoGeometry.OperatorAlgebra.StinespringDilation

noncomputable section

namespace InfoGeometry.OperatorAlgebra.HelicalDivisorStinespring

open InfoGeometry.OperatorAlgebra.TopologicalSnap
open InfoGeometry.OperatorAlgebra.StinespringDilation

/-! ## 1. Helical modular sheets -/

/--
A helical modular phase consists of a local angle and an integer sheet.

The represented unwrapped parameter is morally `angle + 2π * sheet`.
-/
structure HelicalPhase where
  angle : ℝ
  sheet : ℤ
deriving DecidableEq

namespace HelicalPhase

/-- The unwrapped helical modular parameter. -/
def unwrapped
    (h : HelicalPhase) : ℝ :=
  h.angle + (2 * Real.pi) * (h.sheet : ℝ)

/-- Move to the next helical sheet. -/
def nextSheet
    (h : HelicalPhase) : HelicalPhase :=
  { h with sheet := h.sheet + 1 }

/-- Move to the previous helical sheet. -/
def prevSheet
    (h : HelicalPhase) : HelicalPhase :=
  { h with sheet := h.sheet - 1 }

@[simp] theorem nextSheet_angle
    (h : HelicalPhase) :
    h.nextSheet.angle = h.angle :=
  rfl

@[simp] theorem nextSheet_sheet
    (h : HelicalPhase) :
    h.nextSheet.sheet = h.sheet + 1 :=
  rfl

@[simp] theorem prevSheet_angle
    (h : HelicalPhase) :
    h.prevSheet.angle = h.angle :=
  rfl

@[simp] theorem prevSheet_sheet
    (h : HelicalPhase) :
    h.prevSheet.sheet = h.sheet - 1 :=
  rfl

/-- Advancing one sheet adds one full phase period to the unwrapped parameter. -/
theorem unwrapped_nextSheet
    (h : HelicalPhase) :
    h.nextSheet.unwrapped = h.unwrapped + 2 * Real.pi := by
  dsimp [unwrapped, nextSheet]
  norm_num [Int.cast_add]
  ring_nf

/-- Moving back one sheet subtracts one full phase period from the unwrapped parameter. -/
theorem unwrapped_prevSheet
    (h : HelicalPhase) :
    h.prevSheet.unwrapped = h.unwrapped - 2 * Real.pi := by
  dsimp [unwrapped, prevSheet]
  norm_num [Int.cast_sub]
  ring_nf

end HelicalPhase

/-! ## 2. Spectral divisor charges -/

/--
A spectral divisor charge.

`zeroLocus` is the divisor locus.
`multiplicity` is the integer divisor multiplicity or winding contribution.
`chargeOf` is the charge assigned to a region/contour label.
-/
structure SpectralDivisorCharge where
  zeroLocus : Set ℂ
  multiplicity : ℂ → ℤ
  chargeOf : Set ℂ → ℤ
  /--
  Divisor/argument-principle law.

  A concrete implementation should connect this to a contour integral, winding
  number, spectral flow, or scattering phase.
  -/
  divisor_law : Prop

namespace SpectralDivisorCharge

/-- The charge is trivial on a region when its divisor readout is zero. -/
def IsTrivialRegion
    (D : SpectralDivisorCharge)
    (Ω : Set ℂ) : Prop :=
  D.chargeOf Ω = 0

/-- Nonzero charge is exactly nontriviality of the region readout. -/
theorem not_trivialRegion_of_charge_ne_zero
    (D : SpectralDivisorCharge)
    {Ω : Set ℂ}
    (hΩ : D.chargeOf Ω ≠ 0) :
    ¬ D.IsTrivialRegion Ω := by
  intro htrivial
  exact hΩ htrivial

/-- A trivial region has zero charge by definition. -/
theorem charge_eq_zero_of_trivialRegion
    (D : SpectralDivisorCharge)
    {Ω : Set ℂ}
    (hΩ : D.IsTrivialRegion Ω) :
    D.chargeOf Ω = 0 :=
  hΩ

end SpectralDivisorCharge

/-! ## 3. Helical state packets -/

/--
A packet over helical sheets.

This represents a state whose distinguishability/readout is distributed across
multiple modular sheets.
-/
structure HelicalPacket
    (State : Type*) where
  component : ℤ → State
  /-- Support/readout law for the packet. -/
  packet_law : Prop

namespace HelicalPacket

/-- Projection onto one helical sheet. -/
def project
    {State : Type*}
    (P : HelicalPacket State)
    (N : ℤ) : State :=
  P.component N

@[simp] theorem project_eq_component
    {State : Type*}
    (P : HelicalPacket State)
    (N : ℤ) :
    P.project N = P.component N :=
  rfl

end HelicalPacket

/-! ## 4. Divisor charge as a TopologicalSnap obstruction -/

/--
A helical divisor obstruction flow.

This packages a `TopologicalSnap` obstruction whose charge is an integer
sheet/divisor charge.
-/
structure HelicalDivisorObstructionFlow
    (State : Type*) where
  invariant : State → ℤ
  Flat : Set State
  flow : ℝ → State → State
  flat_invariant_zero :
    ∀ x : State, x ∈ Flat → invariant x = 0
  flow_preserves_invariant :
    ∀ t x, invariant (flow t x) = invariant x

/--
Convert a helical divisor obstruction into the generic conserved-obstruction
flow.
-/
def HelicalDivisorObstructionFlow.toConserved
    {State : Type*}
    (H : HelicalDivisorObstructionFlow State) :
    ConservedObstructionFlow State ℤ where
  invariant := H.invariant
  Flat := H.Flat
  flow := H.flow
  flat_invariant_zero := H.flat_invariant_zero
  flow_preserves_invariant := H.flow_preserves_invariant

namespace HelicalDivisorObstructionFlow

variable {State : Type*}
variable (H : HelicalDivisorObstructionFlow State)

/-- A state with nonzero helical/divisor charge cannot relax into the flat sheet. -/
theorem nonzero_sheet_cannot_flow_to_flat
    {x : State}
    (hx : H.invariant x ≠ 0)
    (t : ℝ) :
    H.flow t x ∉ H.Flat :=
  H.toConserved.nontrivial_cannot_flow_to_flat hx t

/-- Landing in the flat sheet forces the initial helical/divisor charge to vanish. -/
theorem invariant_zero_of_flows_to_flat
    {x : State}
    {t : ℝ}
    (hflat : H.flow t x ∈ H.Flat) :
    H.invariant x = 0 :=
  H.toConserved.invariant_zero_of_flows_to_flat hflat

end HelicalDivisorObstructionFlow

/-! ## 5. Stinespring accounting over helical sheets -/

/--
A Stinespring model whose hidden sector is indexed/interpreted by helical
sheet data.

This is the formal version of:

  observed loss on the visible sheet is accounted for by hidden components
  living on other sheets.
-/
structure HelicalStinespringAccounting
    (State Env Joint : Type*)
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    (C : OpenSystemChannel State) where
  dilation : StinespringDilation State Env Joint C
  /-- Assign a helical sheet charge to hidden environment components. -/
  hiddenSheetCharge : Env → ℤ
  /-- Hidden component of a state has the declared sheet charge. -/
  hidden_charge_law : Prop
  /--
  Interpretation law: nonzero hidden sheet charge means hidden/non-flat branch
  information.
  -/
  nonzero_charge_hidden_law : Prop

namespace HelicalStinespringAccounting

variable
    {State Env Joint : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Env] [Module ℝ Env]
    [AddCommGroup Joint] [Module ℝ Joint]
    {C : OpenSystemChannel State}

variable (A : HelicalStinespringAccounting State Env Joint C)

/--
The visible deficit is exactly the mirrored hidden component, inherited from
the concrete Stinespring dilation owner.
-/
theorem visible_deficit_eq_hidden
    (x : State) :
    C.ideal x - C.actual x =
      A.dilation.mirroredHiddenComponent x :=
  A.dilation.ideal_sub_actual_eq_mirroredHidden x

/-- The hidden environment component after joint evolution. -/
def hiddenComponent
    (x : State) : Env :=
  A.dilation.hiddenComponent x

/-- The sheet charge of the hidden environment component of a state. -/
def hiddenSheetChargeOf
    (x : State) : ℤ :=
  A.hiddenSheetCharge (A.hiddenComponent x)

end HelicalStinespringAccounting

/-! ## 6. Spectral-function calibration socket -/

/--
Calibration saying that a concrete spectral determinant or L-function supplies
the divisor charge used by the helical/Stinespring model.

This is where a material scattering determinant, automorphic L-function, or
Riemann-zeta-style readout enters.
-/
structure SpectralFunctionDivisorCalibration
    (State : Type*) where
  /-- Spectral/scattering/L-function readout. -/
  spectralFunction : State → ℂ → ℂ
  /-- Associated divisor charge. -/
  divisorCharge : SpectralDivisorCharge
  /--
  Calibration law connecting zeroes/poles of `spectralFunction` to the integer
  divisor charge.
  -/
  spectral_divisor_law : Prop
  /--
  Optional statement that this function is the intended Riemann/L-function,
  material scattering determinant, or optical transfer determinant.
  -/
  interpretation_law : Prop

namespace SpectralFunctionDivisorCalibration

variable {State : Type*}
variable (C : SpectralFunctionDivisorCalibration State)

end SpectralFunctionDivisorCalibration

end InfoGeometry.OperatorAlgebra.HelicalDivisorStinespring
