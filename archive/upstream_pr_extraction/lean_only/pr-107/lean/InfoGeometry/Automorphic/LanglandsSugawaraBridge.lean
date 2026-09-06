/-
InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean

Witness-gated bridge between affine/Virasoro central-charge readouts and
projected automorphic L-function resonance data.

This module does not prove Langlands, Euler products, functional equations, or
E9 arithmetic. It packages a supplied calibration between a Virasoro/Sugawara
central-charge readout and a completed L-function readout.
-/

import Mathlib.Tactic
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
    (P : ProjectedAutomorphicLFunctionData W)
    (Finite Affine Vir State : Type*)
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State] where

  /-- Strong arithmetic property for the projected L-function. -/
  resonance :
    LanglandsPrimeResonanceStrongData P

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

  This is the true bridge property.
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
    {P : ProjectedAutomorphicLFunctionData W}
    {Finite Affine Vir State : Type*}
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]

variable
    (B : LanglandsSugawaraBridge P Finite Affine Vir State)

/-- Legacy weak Euler-product data read back from the strong property lane. -/
def eulerProduct :
    EulerProductData P.L :=
  B.resonance.eulerProduct.toEulerProductData

/-- Legacy completed L-function read back from the strong property lane. -/
def completedL :
    ℂ → ℂ :=
  B.resonance.completed.completedL

/-- Central charge equals the selected completed L-function value by the supplied
calibration. -/
theorem centralCharge_eq_completedL :
    B.affineVirasoro.centralChargeReadout B.state =
      B.completedL B.spectralPoint := by
  change B.affineVirasoro.centralChargeReadout B.state =
    B.resonance.completed.completedL B.spectralPoint
  exact B.centralCharge_eq_completedL_value

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
      B.affineVirasoro.calibratedHiddenGradeMemoryReadout B.state :=
  B.affineVirasoro.centralCharge_eq_hiddenGradeMemory B.state

/--
Hidden exceptional grade-memory readout equals the selected completed
L-function value.

This is the composed payload:
Virasoro central charge = hidden memory = completed L-value.
-/
theorem hiddenGradeMemory_eq_completedL :
    B.affineVirasoro.calibratedHiddenGradeMemoryReadout B.state =
      B.completedL B.spectralPoint := by
  rw [← B.centralCharge_eq_hiddenGradeMemory]
  exact B.centralCharge_eq_completedL

end LanglandsSugawaraBridge

end InfoGeometry.Automorphic
