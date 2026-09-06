/-
InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean

Witness-gated bridge between affine/Virasoro central-charge readouts and
projected automorphic L-function resonance data.

This module does not prove Langlands, Euler products, functional equations, or
E9 arithmetic. It packages a supplied calibration between a Virasoro/Sugawara
central-charge readout and a completed L-function readout.
-/

import Mathlib
import InfoGeometry.Automorphic.ProjectedLFunction
import InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge

noncomputable section

namespace InfoGeometry.Automorphic

open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge

universe uBulk uBoundary

/--
Witness-gated bridge from affine/Virasoro central charge to completed
automorphic L-function readout.

`State` is the affine/Virasoro boundary state space.

The bridge is deliberately calibrated by a supplied law. It does not derive the
Euler product or completed functional equation from affine/Virasoro data.
-/
structure LanglandsSugawaraBridge
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W)
    (Finite Affine Vir State : Type*)
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State] where

  /-- Strong arithmetic witness for the projected L-function. -/
  resonance :
    LanglandsPrimeResonanceStrongWitness P

  /-- Exceptional affine/Virasoro central-charge bridge with complex readout. -/
  affineVirasoro :
    ExceptionalAffineVirasoroBridge Finite Affine Vir State ℂ

  /-- Boundary state at which the central charge is compared. -/
  state :
    State

  /-- Spectral point at which the completed L-function is evaluated. -/
  spectralPoint :
    ℂ

  /--
  Calibration law: Virasoro/Sugawara central-charge readout equals the selected
  completed L-function value.

  This is the true bridge hypothesis.
  -/
  centralCharge_eq_completedL_value :
    affineVirasoro.centralChargeReadout state =
      resonance.completed.completedL spectralPoint

namespace LanglandsSugawaraBridge

variable
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {P : ProjectedAutomorphicLFunctionWitness W}
    {Finite Affine Vir State : Type*}
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]

variable
    (B : LanglandsSugawaraBridge P Finite Affine Vir State)

/-- Legacy weak Euler-product data read back from the strong witness lane. -/
def eulerProduct :
    EulerProductData P.L :=
  B.resonance.eulerProduct.toEulerProductData

/-- Legacy completed L-function read back from the strong witness lane. -/
def completedL :
    ℂ → ℂ :=
  B.resonance.completed.completedL

/-- Legacy completed-functional-equation witness read back from the strong witness lane. -/
theorem completedFunctionalEquation :
    HasCompletedFunctionalEquation P.L B.completedL :=
  B.resonance.completed.toHasCompletedFunctionalEquation

/--
The bridge packages the supplied Euler/completed data as a
`LanglandsPrimeResonanceWitness`.
-/
def toLanglandsPrimeResonanceWitness :
    LanglandsPrimeResonanceWitness P :=
  B.resonance.toWeakWitness

/--
Central charge equals the selected completed L-function value by the supplied
calibration.
-/
theorem centralCharge_eq_completedL :
    B.affineVirasoro.centralChargeReadout B.state =
      B.completedL B.spectralPoint :=
  B.centralCharge_eq_completedL_value

/--
If the completed L-function on the bridge is identified with the projected
L-function and the spectral point is `0`, then the central charge readout is
the projected value at `0`.
-/
theorem centralCharge_eq_projectedL_zero_of_match
    (B : LanglandsSugawaraBridge P Finite Affine Vir State)
    (hspectral : B.spectralPoint = 0)
    (hcompleted : B.completedL = P.L) :
    B.affineVirasoro.centralChargeReadout B.state = P.L 0 := by
  simpa [hspectral, hcompleted] using B.centralCharge_eq_completedL

/--
Central charge also equals hidden exceptional grade-memory readout by the
affine/Virasoro exceptional bridge.
-/
theorem centralCharge_eq_hiddenGradeMemory :
    B.affineVirasoro.centralChargeReadout B.state =
      B.affineVirasoro.hiddenGradeMemoryReadout B.state :=
  B.affineVirasoro.centralCharge_eq_hiddenGradeMemory B.state

/--
Hidden exceptional grade-memory readout equals the selected completed
L-function value.

This is the composed payload:
Virasoro central charge = hidden memory = completed L-value.
-/
theorem hiddenGradeMemory_eq_completedL :
    B.affineVirasoro.hiddenGradeMemoryReadout B.state =
      B.completedL B.spectralPoint := by
  rw [← B.centralCharge_eq_hiddenGradeMemory]
  exact B.centralCharge_eq_completedL

end LanglandsSugawaraBridge

/--
Installed owner target for the Langlands/Sugawara bridge.

Once the bridge witness is supplied, it packages the strong
`LanglandsPrimeResonanceStrongWitness` already carried by the bridge and
exposes the central-charge/completed-L calibration.
-/
structure LanglandsSugawaraBridgeInstalledTarget
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W)
    (Finite Affine Vir State : Type*)
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (B : LanglandsSugawaraBridge P Finite Affine Vir State) where
  /-- Strong resonance witness already carried by the bridge. -/
  strongWitness : LanglandsPrimeResonanceStrongWitness P

  /-- Central charge calibration carried by the bridge. -/
  centralCharge_eq_completedL :
    B.affineVirasoro.centralChargeReadout B.state =
      B.completedL B.spectralPoint

/--
The installed target data follows from the supplied bridge witness.
-/
def langlandsSugawaraBridgeInstalledTarget :
    ∀ {Bulk : Type uBulk} {Boundary : Type uBoundary}
      [AddCommGroup Bulk] [Module ℝ Bulk]
      [AddCommGroup Boundary] [Module ℝ Boundary]
      {W : SiegelEisensteinWitness Bulk Boundary}
      (P : ProjectedAutomorphicLFunctionWitness W)
      (Finite Affine Vir State : Type*)
      [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
      [AddCommGroup State] [Module ℝ State]
      (B : LanglandsSugawaraBridge P Finite Affine Vir State),
    LanglandsSugawaraBridgeInstalledTarget
      (P := P) (Finite := Finite) (Affine := Affine) (Vir := Vir) (State := State) B := by
  intro Bulk Boundary _ _ _ _ W P Finite Affine Vir State _ _ _ _ _ _ B
  exact
    { strongWitness := B.resonance,
      centralCharge_eq_completedL := B.centralCharge_eq_completedL }

end InfoGeometry.Automorphic
