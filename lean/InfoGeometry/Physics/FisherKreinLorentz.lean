import Mathlib.Algebra.Order.BigOperators.Group.Finset
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Explicit Fisher-Krein Lorentz readout

This file implements the finite `Fin 4` readout used in the Souriau/free-entropy
roadmap:

* start with the positive Fisher unit matrix;
* choose the modular-time covector `e₀`;
* reflect by `G - 2 e₀ e₀ᵀ`;
* obtain the diagonal `(-1, 1, 1, 1)` Lorentz readout.

The result is a concrete signed pullback layer, not a claim that a full
Einstein-Hilbert action has already been induced.
-/

namespace InfoGeometry.Physics.FisherKreinLorentz

open Finset
open scoped BigOperators

noncomputable section

abbrev Index4 : Type :=
  Fin 4

/-- Kronecker delta on `Fin 4`, as a real scalar. -/
def delta4 (i j : Index4) : ℝ :=
  if i = j then 1 else 0

/-- The distinguished modular-time covector. -/
def modularTimeCovector4 (i : Index4) : ℝ :=
  if i = 0 then 1 else 0

/-- Positive Fisher unit matrix. -/
def fisherUnit4 (i j : Index4) : ℝ :=
  delta4 i j

/-- Krein reflection of a Fisher matrix along a chosen covector. -/
def fisherKreinReflect4
    (fisher : Index4 → Index4 → ℝ) (timeCovector : Index4 → ℝ)
    (i j : Index4) : ℝ :=
  fisher i j - 2 * timeCovector i * timeCovector j

/-- The explicit `(-,+,+,+)` Fisher-Krein Lorentz matrix. -/
def fisherKreinLorentz4 (i j : Index4) : ℝ :=
  fisherKreinReflect4 fisherUnit4 modularTimeCovector4 i j

@[simp] theorem delta4_self (i : Index4) :
    delta4 i i = 1 := by
  simp [delta4]

theorem delta4_of_ne {i j : Index4} (hij : i ≠ j) :
    delta4 i j = 0 := by
  simp [delta4, hij]

@[simp] theorem modularTimeCovector4_zero :
    modularTimeCovector4 0 = 1 := by
  simp [modularTimeCovector4]

theorem modularTimeCovector4_of_ne_zero {i : Index4} (hi : i ≠ 0) :
    modularTimeCovector4 i = 0 := by
  simp [modularTimeCovector4, hi]

/-- The modular-time entry is negative. -/
theorem fisherKreinLorentz4_time_time :
    fisherKreinLorentz4 0 0 = -1 := by
  norm_num [fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4, delta4,
    modularTimeCovector4]

/-- Every non-time diagonal entry is positive. -/
theorem fisherKreinLorentz4_spatial_diag {i : Index4} (hi : i ≠ 0) :
    fisherKreinLorentz4 i i = 1 := by
  simp [fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4, delta4,
    modularTimeCovector4, hi]

/-- Off-diagonal entries vanish. -/
theorem fisherKreinLorentz4_offdiag {i j : Index4} (hij : i ≠ j) :
    fisherKreinLorentz4 i j = 0 := by
  by_cases hi : i = 0
  · subst hi
    have hj : j ≠ 0 := by
      intro h
      exact hij (by simp [h])
    simp [fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4, delta4,
      modularTimeCovector4, hij, hj]
  · by_cases hj : j = 0
    · subst hj
      simp [fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4, delta4,
        modularTimeCovector4, hij]
    · simp [fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4, delta4,
        modularTimeCovector4, hij, hi, hj]

/-- Pullback of a target metric by an explicit Jacobian `dβ`. -/
def pullbackMetric4
    (dBeta : Index4 → Index4 → ℝ) (targetMetric : Index4 → Index4 → ℝ)
    (mu nu : Index4) : ℝ :=
  ∑ a : Index4, ∑ b : Index4, dBeta mu a * targetMetric a b * dBeta nu b

/-- Identity Jacobian on `Fin 4`. -/
def identityJacobian4 (mu a : Index4) : ℝ :=
  delta4 mu a

/-- Pullback by the identity Jacobian returns the target metric. -/
theorem pullbackMetric4_identity_fisherKreinLorentz
    (mu nu : Index4) :
    pullbackMetric4 identityJacobian4 fisherKreinLorentz4 mu nu =
      fisherKreinLorentz4 mu nu := by
  fin_cases mu <;> fin_cases nu <;>
    norm_num [pullbackMetric4, identityJacobian4, delta4, fisherKreinLorentz4,
      fisherKreinReflect4, fisherUnit4, modularTimeCovector4]

/-- Scalar residual for an Einstein equation corrected by a quantum-state tensor readout. -/
def quantumCorrectedEinsteinResidual
    (einsteinTensor newtonG effectiveStress hbar quantumStateTensor : ℝ) : ℝ :=
  einsteinTensor -
    ((8 * Real.pi * newtonG) * effectiveStress + hbar * quantumStateTensor)

/-- Zero residual is exactly the scalar quantum-corrected Einstein balance. -/
theorem quantumCorrectedEinsteinResidual_eq_zero_iff
    (einsteinTensor newtonG effectiveStress hbar quantumStateTensor : ℝ) :
    quantumCorrectedEinsteinResidual
        einsteinTensor newtonG effectiveStress hbar quantumStateTensor = 0 ↔
      einsteinTensor =
        (8 * Real.pi * newtonG) * effectiveStress + hbar * quantumStateTensor := by
  unfold quantumCorrectedEinsteinResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith

end

end InfoGeometry.Physics.FisherKreinLorentz
