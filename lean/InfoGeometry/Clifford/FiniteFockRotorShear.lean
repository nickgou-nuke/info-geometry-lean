/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteFockCLMReflexivePair
import InfoGeometry.Canonical.ReflexiveRotorRealTime

/-! Native Fock spinor readback, Stream5 idempotence and Stream4 quarter-turn.
No new flow or spinor carrier is defined. No analytic proof is duplicated. -/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
open InfoGeometry.Canonical.ReflexiveRotorRealTime
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

variable (n : ℕ) (i : Fin n)
local notation "D" => fockIntActionCLM n i
local notation "C" => fockExtActionCLM n i

/-- Stream5 and the native real rotor are the same operator at circle parameters. -/
theorem fock_phaseRotor_eq_realRotor (t : ℝ) :
    phaseRotor (Real.cos t) (Real.sin t) D C = realRotor D C t := rfl

/-- CAR removes the inactive complement on the actual spinor endomorphism algebra. -/
theorem fock_realRotor_eq (t : ℝ) :
    realRotor D C t = Real.cos t • 1 + Real.sin t • (D - C) := by
  simp only [realRotor, InfoGeometry.Canonical.ReflexiveNilpotentFlows.rotor,
    InfoGeometry.Canonical.ReflexiveNilpotentFlows.complement,
    InfoGeometry.Canonical.ReflexiveNilpotentFlows.support,
    fock_coordinate_CLM_CAR, sub_self, zero_add]

/-- Direct action on every original spinor, with contraction minus creation. -/
theorem fock_realRotor_apply (t : ℝ) (x : SpinorSpace (Vector n)) :
    realRotor D C t x = Real.cos t • x + Real.sin t • (D x - C x) := by
  rw [fock_realRotor_eq]
  rfl

/-- Stream5's moving pole is the actual native conjugation trajectory. -/
theorem fock_movingPolePlus_eq_conjugationPath (t : ℝ) :
    movingPolePlus (Real.cos t) (Real.sin t) D C =
      InfoGeometry.Canonical.ModularFlowGeneratorDerivative.conjugationPath
        (realRotor D C) (fun s => realRotor D C (-s)) (D * C) t := by
  change phaseRotor (Real.cos t) (Real.sin t) D C * (D * C) *
      phaseRotor (Real.cos t) (-Real.sin t) D C =
    realRotor D C t * (D * C) * realRotor D C (-t)
  rw [fock_phaseRotor_eq_realRotor, realRotor_neg]
  rfl

/-- Explicit moving coordinate-vacancy action, not a full many-mode vacuum claim. -/
theorem fock_movingPolePlus_apply (t : ℝ) (x : SpinorSpace (Vector n)) :
    movingPolePlus (Real.cos t) (Real.sin t) D C x =
      (Real.cos t * Real.cos t) • D (C x) +
      (Real.sin t * Real.sin t) • C (D x) -
      (Real.cos t * Real.sin t) • (D x + C x) := by
  rw [movingPolePlus_eq (fock_isDualSeedPair n i)]
  rfl

/-- Actual circle parameters yield an idempotent operator on the native spinors. -/
theorem fock_movingPolePlus_idempotent (t : ℝ) :
    movingPolePlus (Real.cos t) (Real.sin t) D C *
      movingPolePlus (Real.cos t) (Real.sin t) D C =
      movingPolePlus (Real.cos t) (Real.sin t) D C := by
  apply movingPolePlus_idem (fock_isDualSeedPair n i)
  simpa only [pow_two] using Real.cos_sq_add_sin_sq t

/-- Stream4's ordered double shear acts on the same spinor, with the DC term. -/
theorem fock_doubleShear_apply (x : SpinorSpace (Vector n)) :
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.parabolicHexalityOp D C x =
      x + D x - C x - D (C x) := by
  change (1 + D) ((1 - C) x) = _
  change (x - C x) + D (x - C x) = _
  rw [map_sub]
  abel

/-- The native triple shear is exactly the skew coordinate generator. -/
theorem fock_tripleShear_eq :
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.bruhatQuarticOp D C =
      D - C := by
  rw [InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.bruhatQuarticOp_eq_zeroMode_add_sub
    (fock_isDualRootOfZeroPair n i)]
  simp only [InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.poleZeroMode,
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.activeSupport,
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.polePlus,
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.poleMinus,
    fock_coordinate_CLM_CAR, sub_self, zero_add]

/-- Discrete Stream4 shear equals a quarter-turn of the actual real-time rotor. -/
theorem fock_tripleShear_eq_quarterTurn :
    InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.bruhatQuarticOp D C =
      realRotor D C (Real.pi / 2) := by
  rw [fock_tripleShear_eq, fock_realRotor_eq]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]

/-- Direct quarter-turn application, retaining the native contraction/creation maps. -/
theorem fock_quarterTurn_apply (x : SpinorSpace (Vector n)) :
    realRotor D C (Real.pi / 2) x = D x - C x := by
  rw [fock_realRotor_apply]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
