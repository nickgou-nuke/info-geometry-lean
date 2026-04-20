import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Canonical.BogoliubovTransport
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.OperatorialHessianBridge

Bridge module between operator-valued Lie Hessians and scalar log-readout readouts.

This module formalizes the Tier 2 Readout established in Chapter 156:
- Scalar Log-Readout: F_A(t) = log ω(α_t^X(A))

This file provides the verified first derivative of the log-readout.
The second derivative (Information-Geometric Norm) remains a named target.
-/

namespace InfoGeometry.Canonical.OperatorialHessianBridge

open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData
open InfoGeometry.Canonical
open InfoGeometry.Krein

section Bridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Logarithmic modular response functional (Tier 2 Scalar Readout). -/
@[rep_depth transport]
noncomputable def scalarLogReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  Real.log (ω (transportedObservable (E := E) X A t))

/--
The first derivative of the scalar log-readout at t=0 is the
expectation of the first information variation (normalized).
-/
@[rep_depth transport]
theorem hasDerivAt_scalarLogReadout_zero
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hA : ω A = 1) :
    let δA := operatorInformationFirstVariation (E := E) X A
    HasDerivAt (fun t => scalarLogReadout (E := E) ω X A t) (ω δA) 0 := by
  unfold scalarLogReadout
  let f := fun t => ω (transportedObservable (E := E) X A t)
  have h_transport :
      HasDerivAt (fun t => transportedObservable (E := E) X A t) ⁅X, A⁆ 0 :=
    hasDerivAt_expTransport_at_zero X A
  have hf : HasDerivAt f (ω ⁅X, A⁆) 0 := by
    let ω_const : ℝ → (EndH →L[ℝ] ℝ) := fun _ => ω
    have hω_const : HasDerivAt ω_const 0 0 := hasDerivAt_const 0 ω
    simpa using hω_const.clm_apply h_transport
  have hf0 : f 0 = 1 := by
    simp [f, transportedObservable, expTransport, hA]
  have hLog : HasDerivAt Real.log 1 (f 0) := by
    rw [hf0]
    simpa using Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)
  have hcomp := hLog.comp 0 hf
  dsimp
  simpa [operatorInformationFirstVariation, lieBracket_eq_transportCommutator] using hcomp

end Bridge

end InfoGeometry.Canonical.OperatorialHessianBridge
