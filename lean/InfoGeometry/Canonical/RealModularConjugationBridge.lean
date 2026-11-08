/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealTomitaCore

/-!
# Modular conjugation, logarithmic inversion, and opposite operator shells

This module extends the existing bounded-operator `RealModularLogData` owner.
Its hypothesis is the logarithmic Tomita relation `J δ = -δ J`.  The phase axis
already satisfies `J I = -I J` on the repository's real doubled carrier.
Consequently the transport generator `δ I` commutes with `J`, and conjugation
preserves the real parameter of the exponential transport flow.

The opposite signs in the focused and defocused shell definitions then give
`J O_foc(t) J = O_defoc(-t)`.  That sign comes from the two shell conventions;
it is not a claim that anti-linear Tomita conjugation reverses `Delta^(it)`.

`RealModularLogData` supplies an exponential certificate, not a spectral
logarithm, positivity, a cyclic separating state, or a von Neumann commutant
identification.  Those additional standard-form hypotheses remain separate.
No limiting wavefront, KMS analytic continuation, or chiral-ideal convergence
is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealModularConjugationBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.RealTomitaCore
open InfoGeometry.Canonical.BogoliubovTransport

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E
local notation "J" => InfoGeometry.Krein.modular_j (E := E)
local notation "Iop" => InfoGeometry.Krein.clockAxis (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

private theorem modular_j_mul_self : J * J = (1 : EndH) :=
  modular_j_involution E

/-- Conjugation by the fixed real Tomita involution is involutive on operators. -/
theorem commutantAction_involutive (A : EndH) :
    commutantAction (commutantAction A) = A := by
  simp only [commutantAction]
  calc
    J * (J * A * J) * J = (J * J) * A * (J * J) := by
      simp only [mul_assoc]
    _ = A := by rw [modular_j_mul_self]; simp

namespace RealModularLogData

variable (T : InfoGeometry.Canonical.RealTomitaCore.RealModularLogData (E := E))

/-- The exponential certificate makes `Delta` invertible in the operator ring. -/
theorem isUnit_Delta : IsUnit T.Delta := by
  rw [← T.exp_deltaLog]
  exact NormedSpace.isUnit_exp T.deltaLog

/-- The explicit logarithmic oddness hypothesis gives `J deltaLog J = -deltaLog`. -/
theorem commutantAction_deltaLog
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) :
    commutantAction T.deltaLog = -T.deltaLog := by
  unfold commutantAction
  calc
    J * T.deltaLog * J = -(T.deltaLog * J) * J := by rw [hδ]
    _ = -(T.deltaLog * (J * J)) := by rw [neg_mul, mul_assoc]
    _ = -T.deltaLog := by rw [modular_j_mul_self, mul_one]

/-- Exponentiation transports the logarithmic sign to inversion of `Delta`. -/
theorem commutantAction_Delta_eq_exp_neg
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) :
    commutantAction T.Delta = NormedSpace.exp (-T.deltaLog) := by
  have hs : SemiconjBy J T.deltaLog (-T.deltaLog) := by
    change J * T.deltaLog = (-T.deltaLog) * J
    rw [neg_mul]
    exact hδ
  have he : J * NormedSpace.exp T.deltaLog = NormedSpace.exp (-T.deltaLog) * J :=
    hs.exp_right
  unfold commutantAction
  rw [← T.exp_deltaLog, he, mul_assoc, modular_j_mul_self, mul_one]

/-- The reflected exponential is the genuine ring inverse, on the same carrier. -/
theorem commutantAction_Delta_eq_inverse
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) :
    commutantAction T.Delta = Ring.inverse T.Delta := by
  rw [commutantAction_Delta_eq_exp_neg T hδ, ← T.exp_deltaLog, Ring.inverse_exp]

/-- Left inverse law, with invertibility derived from the exponential certificate. -/
theorem commutantAction_Delta_mul_Delta
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) :
    commutantAction T.Delta * T.Delta = 1 := by
  rw [commutantAction_Delta_eq_exp_neg T hδ, ← T.exp_deltaLog,
    ← NormedSpace.exp_add_of_commute (Commute.refl T.deltaLog).neg_left]
  simp

/-- Right inverse law for the same reflected operator. -/
theorem Delta_mul_commutantAction_Delta
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) :
    T.Delta * commutantAction T.Delta = 1 := by
  rw [commutantAction_Delta_eq_exp_neg T hδ, ← T.exp_deltaLog,
    ← NormedSpace.exp_add_of_commute (Commute.refl T.deltaLog).neg_right]
  simp

/-- Both the logarithm and the phase axis are `J`-odd, so their product is even. -/
theorem modular_j_commutes_generator
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) :
    Commute J T.generator := by
  have hI : J * Iop = -(Iop * J) :=
    InfoGeometry.Krein.modular_j_complex_i_anticommute (E := E)
  change J * (T.deltaLog * Iop) = (T.deltaLog * Iop) * J
  calc
    J * (T.deltaLog * Iop) = (J * T.deltaLog) * Iop := by
      rw [mul_assoc]
    _ = -(T.deltaLog * (J * Iop)) := by rw [hδ, neg_mul, mul_assoc]
    _ = -(T.deltaLog * -(Iop * J)) := by rw [hI]
    _ = (T.deltaLog * Iop) * J := by rw [mul_neg, neg_neg, mul_assoc]

/-- Exponentiating the even transport generator preserves commutation with `J`. -/
theorem modular_j_commutes_flow
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) (t : ℝ) :
    Commute J (T.flow t) := by
  have hs : Commute J (t • T.generator) := by
    change J * (t • T.generator) = (t • T.generator) * J
    calc
      J * (t • T.generator) = t • (J * T.generator) := by
        change (J).comp (t • T.generator) = t • (J).comp T.generator
        exact ContinuousLinearMap.comp_smul J t T.generator
      _ = t • (T.generator * J) := by
        rw [(modular_j_commutes_generator T hδ).eq]
      _ = (t • T.generator) * J := by
        change t • T.generator.comp J = (t • T.generator).comp J
        exact (ContinuousLinearMap.smul_comp t T.generator J).symm
  have h := hs.exp_right
  simpa only [InfoGeometry.Canonical.RealTomitaCore.RealModularLogData.flow,
    InfoGeometry.Canonical.RealTomitaCore.RealModularLogData.generator,
    modularTransportFlow] using h

/-- Conjugation fixes the chosen real exponential flow, with its parameter unchanged. -/
theorem commutantAction_flow
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) (t : ℝ) :
    commutantAction (T.flow t) = T.flow t := by
  unfold commutantAction
  rw [(modular_j_commutes_flow T hδ t).eq, mul_assoc, modular_j_mul_self, mul_one]

/-- The same-parameter conjugation law passes to the observable adjoint flow. -/
theorem commutantAction_adjointFlow
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) (t : ℝ) (A : EndH) :
    commutantAction (T.adjointFlow t A) = T.adjointFlow t (commutantAction A) := by
  unfold commutantAction InfoGeometry.Canonical.RealTomitaCore.RealModularLogData.adjointFlow
  calc
    J * (T.flow t * A * T.flow (-t)) * J =
        (J * T.flow t) * A * (T.flow (-t) * J) := by
      simp only [mul_assoc]
    _ = (T.flow t * J) * A * (J * T.flow (-t)) := by
      rw [(modular_j_commutes_flow T hδ t).eq,
        ← (modular_j_commutes_flow T hδ (-t)).eq]
    _ = T.flow t * (J * A * J) * T.flow (-t) := by
      simp only [mul_assoc]

/-- Focused operator shell, with its chosen negative transport orientation. -/
def focusedShell (A : EndH) (t : ℝ) : EndH := T.adjointFlow (-t) A

/-- Defocused operator shell of the reflected seed, with positive orientation. -/
def defocusedShell (A : EndH) (t : ℝ) : EndH :=
  T.adjointFlow t (commutantAction A)

/-- Opposite shell orientations produce the requested reflected-parameter identity. -/
theorem commutantAction_focusedShell
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) (A : EndH) (t : ℝ) :
    commutantAction (focusedShell T A t) = defocusedShell T A (-t) := by
  exact commutantAction_adjointFlow T hδ (-t) A

/-- Reflection in the other direction follows from the same operator theorem. -/
theorem commutantAction_defocusedShell
    (hδ : J * T.deltaLog = -(T.deltaLog * J)) (A : EndH) (t : ℝ) :
    commutantAction (defocusedShell T A t) = focusedShell T A (-t) := by
  simp only [defocusedShell, focusedShell, neg_neg,
    commutantAction_adjointFlow T hδ, commutantAction_involutive]

end RealModularLogData

end InfoGeometry.Canonical.RealModularConjugationBridge
