import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Canonical.BogoliubovTransport
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Meta.Architecture

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.OperatorialHessianBridge

Bridge module between operator-valued Lie Hessians and scalar log-readout readouts.

This module formalizes the Tier 2 Readout established in Chapter 156:
- Scalar Log-Readout: F_A(t) = log ω(α_t^X(A))

This file provides the verified first derivative of the log-readout
and formalizes the Bogoliubov-Kubo-Mori (BKM) metric proxy via the
double transport commutator.
-/

namespace OperatorialHessianBridge

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

/-- Scalar, non-logarithmic transport readout underlying `scalarLogReadout`. -/
@[rep_depth transport]
noncomputable def scalarTransportReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  ω (transportedObservable (E := E) X A t)

/--
The scalar transport readout differentiates to the readout of the transported
first Lie variation at every time.
-/
@[rep_depth transport]
theorem hasDerivAt_scalarTransportReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => scalarTransportReadout (E := E) ω X A s)
      (ω (transportedObservable (E := E) X ⁅X, A⁆ t))
      t := by
  let ω_const : ℝ → (EndH →L[ℝ] ℝ) := fun _ => ω
  have hω_const : HasDerivAt ω_const 0 t := hasDerivAt_const t ω
  have hTransport :
      HasDerivAt
        (fun s : ℝ => transportedObservable (E := E) X A s)
        (transportedObservable (E := E) X ⁅X, A⁆ t)
        t := by
    simpa [transportedObservable] using
      (hasDerivAt_expTransport (A := EndH) X A t)
  simpa [scalarTransportReadout] using hω_const.clm_apply hTransport

/-- Derivative form of `hasDerivAt_scalarTransportReadout`. -/
@[rep_depth transport]
theorem deriv_scalarTransportReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) :
    deriv (fun s : ℝ => scalarTransportReadout (E := E) ω X A s) t
      = ω (transportedObservable (E := E) X ⁅X, A⁆ t) :=
  (hasDerivAt_scalarTransportReadout (E := E) ω X A t).deriv

/--
The second scalar transport variation is the scalar readout of the operatorial
Lie Hessian.
-/
@[rep_depth transport]
theorem deriv2_scalarTransportReadout_zero
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) :
    deriv
        (fun t : ℝ =>
          deriv (fun s : ℝ => scalarTransportReadout (E := E) ω X A s) t)
        0
      =
    ω (operatorInformationHessian (E := E) X A) := by
  have hDeriv :
      (fun t : ℝ =>
          deriv (fun s : ℝ => scalarTransportReadout (E := E) ω X A s) t)
        =
      fun t : ℝ => scalarTransportReadout (E := E) ω X ⁅X, A⁆ t := by
    funext t
    exact deriv_scalarTransportReadout (E := E) ω X A t
  rw [hDeriv]
  have hFirst :=
    deriv_scalarTransportReadout (E := E) ω X ⁅X, A⁆ 0
  simpa [scalarTransportReadout, transportedObservable, expTransport,
    operatorInformationHessian, lieBracket_eq_transportCommutator] using hFirst

/--
At nonzero scalar readout values, the derivative of the scalar log-readout is
the logarithmic derivative of the scalar transport readout.
-/
@[rep_depth transport]
theorem deriv_scalarLogReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hNonzero : ∀ t : ℝ, scalarTransportReadout (E := E) ω X A t ≠ 0)
    (t : ℝ) :
    deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t
      =
    deriv (fun s : ℝ => scalarTransportReadout (E := E) ω X A s) t
      / scalarTransportReadout (E := E) ω X A t := by
  have hDiff :
      DifferentiableAt ℝ
        (fun s : ℝ => scalarTransportReadout (E := E) ω X A s) t :=
    (hasDerivAt_scalarTransportReadout (E := E) ω X A t).differentiableAt
  unfold scalarLogReadout scalarTransportReadout
  simpa using
    (deriv.log
      (f := fun s : ℝ => ω (transportedObservable (E := E) X A s))
      hDiff
      (by simpa [scalarTransportReadout] using hNonzero t))

/--
General scalar second-derivative formula for the logarithmic transport readout.

This is the scalar log-Hessian bridge: the numerator is the operatorial Lie
Hessian readout minus the square of the first Lie-variation readout, normalized
by the scalar transport readout.
-/
@[rep_depth transport]
theorem deriv2_scalarLogReadout_zero
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hNonzero : ∀ t : ℝ, scalarTransportReadout (E := E) ω X A t ≠ 0) :
    deriv
        (fun t : ℝ =>
          deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t)
        0
      =
    (ω (operatorInformationHessian (E := E) X A) * scalarTransportReadout (E := E) ω X A 0
      - (ω (operatorInformationFirstVariation (E := E) X A)) ^ (2 : ℕ))
      / (scalarTransportReadout (E := E) ω X A 0) ^ (2 : ℕ) := by
  let f := fun t : ℝ => scalarTransportReadout (E := E) ω X A t
  let g := fun t : ℝ => deriv f t
  have hLogDeriv :
      (fun t : ℝ =>
          deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t)
        =
      fun t : ℝ => g t / f t := by
    funext t
    simpa [f, g] using
      deriv_scalarLogReadout (E := E) ω X A hNonzero t
  rw [hLogDeriv]
  have hgDiff : DifferentiableAt ℝ g 0 := by
    have hDeriv :
        g = fun t : ℝ => scalarTransportReadout (E := E) ω X ⁅X, A⁆ t := by
      funext t
      exact deriv_scalarTransportReadout (E := E) ω X A t
    rw [hDeriv]
    exact (hasDerivAt_scalarTransportReadout (E := E) ω X ⁅X, A⁆ 0).differentiableAt
  have hfDiff : DifferentiableAt ℝ f 0 :=
    (hasDerivAt_scalarTransportReadout (E := E) ω X A 0).differentiableAt
  have hf0 : f 0 ≠ 0 := hNonzero 0
  have hquot :
      deriv (fun t : ℝ => g t / f t) 0 =
        (deriv g 0 * f 0 - g 0 * deriv f 0) / (f 0) ^ (2 : ℕ) := by
    simpa using deriv_div (c := g) (d := f) (x := 0) hgDiff hfDiff hf0
  rw [hquot]
  have hg0 :
      g 0 = ω (operatorInformationFirstVariation (E := E) X A) := by
    simpa [g, f, scalarTransportReadout, transportedObservable, expTransport,
      operatorInformationFirstVariation, lieBracket_eq_transportCommutator] using
      deriv_scalarTransportReadout (E := E) ω X A 0
  have hfderiv0 :
      deriv f 0 = ω (operatorInformationFirstVariation (E := E) X A) := by
    simpa [f, scalarTransportReadout, transportedObservable, expTransport,
      operatorInformationFirstVariation, lieBracket_eq_transportCommutator] using
      deriv_scalarTransportReadout (E := E) ω X A 0
  have hgderiv0 :
      deriv g 0 = ω (operatorInformationHessian (E := E) X A) := by
    simpa [g, f] using deriv2_scalarTransportReadout_zero (E := E) ω X A
  rw [hg0, hfderiv0, hgderiv0]
  ring

/--
Normalized stationary scalar log-Hessian bridge. If the scalar readout is
normalized at the seed and the first scalar Lie variation vanishes, the scalar
second derivative of the logarithmic readout is exactly the probe of the
operatorial Lie Hessian.
-/
@[rep_depth transport]
theorem deriv2_scalarLogReadout_zero_eq_probe_operatorInformationHessian_of_stationary
    (ω : EndH →L[ℝ] ℝ) (X A : EndH)
    (hNonzero : ∀ t : ℝ, scalarTransportReadout (E := E) ω X A t ≠ 0)
    (hNorm : ω A = 1)
    (hStationary : ω (operatorInformationFirstVariation (E := E) X A) = 0) :
    deriv
        (fun t : ℝ =>
          deriv (fun s : ℝ => scalarLogReadout (E := E) ω X A s) t)
        0
      =
    ω (operatorInformationHessian (E := E) X A) := by
  rw [deriv2_scalarLogReadout_zero (E := E) ω X A hNonzero]
  have hf0 : scalarTransportReadout (E := E) ω X A 0 = 1 := by
    simpa [scalarTransportReadout, transportedObservable, expTransport] using hNorm
  rw [hf0, hStationary]
  ring

/--
Support-restricted modular form of the scalar log-Hessian theorem.

For the certified modular generator `Kambient`, the normalized stationary scalar
second derivative of the log-readout is the probe of the certified modular Lie
Hessian. This is the owner bridge from scalar second variation to the
operatorial modular Hessian; no finite response matrix is used.
-/
@[rep_depth transport, capstone]
theorem deriv2_scalarLogReadout_zero_eq_probe_modularLieHessian_of_stationary
    (c : CertifiedModularReduction (E := H₂))
    (ω : EndH →L[ℝ] ℝ) (A : EndH)
    (hNonzero :
      ∀ t : ℝ,
        scalarTransportReadout (E := E) ω (CertifiedModularReduction.Kambient c) A t ≠ 0)
    (hNorm : ω A = 1)
    (hStationary :
      ω (operatorInformationFirstVariation (E := E)
        (CertifiedModularReduction.Kambient c) A) = 0) :
    deriv
        (fun t : ℝ =>
          deriv
            (fun s : ℝ =>
              scalarLogReadout (E := E) ω
                (CertifiedModularReduction.Kambient c) A s)
            t)
        0
      =
    ω (CertifiedModularReduction.modularLieHessian (c := c) A) := by
  rw [deriv2_scalarLogReadout_zero_eq_probe_operatorInformationHessian_of_stationary
    (E := E) ω (CertifiedModularReduction.Kambient c) A hNonzero hNorm hStationary]
  rw [InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian_eq_double_transportCommutator]
  rw [CertifiedModularReduction.modularLieHessian_eq_nested_commutator (c := c) A]
  rw [lieBracket_eq_transportCommutator]
  rw [lieBracket_eq_transportCommutator]

/--
The Operatorial Information Hessian (BKM metric proxy) is the double
transport commutator.
-/
@[rep_depth transport]
def operatorInformationHessian (X A : EndH) : EndH :=
  ⁅X, ⁅X, A⁆⁆

/--
Observable Lie Hessian matching the standard double Lie bracket.
-/
@[rep_depth transport]
def observableLieHessian (X A : EndH) : EndH :=
  X * (X * A - A * X) - (X * A - A * X) * X

/--
The Operatorial Information Hessian matches the explicit double transport
commutator (the formalization of the Bogoliubov-Kubo-Mori BKM metric proxy).
-/
@[rep_depth transport]
theorem operatorInformationHessian_eq_double_transportCommutator (X A : EndH) :
    operatorInformationHessian (E := E) X A = transportCommutator X (transportCommutator X A) := by
  unfold operatorInformationHessian
  rw [← lieBracket_eq_transportCommutator, ← lieBracket_eq_transportCommutator]

/--
The Operatorial Information Hessian equals the raw algebraic Lie Hessian.
-/
@[rep_depth transport]
theorem operatorInformationHessian_eq_observableLieHessian (X A : EndH) :
    operatorInformationHessian (E := E) X A = observableLieHessian X A := by
  unfold operatorInformationHessian observableLieHessian
  simp only [Ring.lie_def]

end Bridge

end OperatorialHessianBridge
