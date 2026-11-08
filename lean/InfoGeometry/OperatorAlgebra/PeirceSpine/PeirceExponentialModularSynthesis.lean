/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorTimeArchetypes
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset

/-!
# Exact Peirce exponential, modular-flow, and defect synthesis

This module assembles existing arbitrary-ring Peirce identities on one carrier:
unitized square-zero corner group laws, the logistic/idempotency-defect readout,
the ordered curvature sandwich, its inner derivation on both boundary corners,
and phase conjugation of cross-corner correlations. The statements are
associative-ring identities; they do not assert an analytic exponential,
continuous modular automorphism group, state, or KMS condition.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset

variable {B : Type*} [Ring B]

/-- Division-free unitization of the upper square-zero Peirce corner. -/
def upperCornerUnit (P A : B) : B := 1 + conePlus P A

/-- Division-free unitization of the lower square-zero Peirce corner. -/
def lowerCornerUnit (P C : B) : B := 1 + coneMinus P C

/-- The exact algebraic package behind the discrete Peirce exponential
families and their logistic defect readout. The group laws use only the
square-zero corner relations in an arbitrary associative ring. -/
theorem corner_unipotent_logistic_defect_laws
    {P : B} (hP : P * P = P) (A₁ A₂ A C : B) :
    upperCornerUnit P A₁ * upperCornerUnit P A₂ =
        upperCornerUnit P (A₁ + A₂) ∧
    upperCornerUnit P A * upperCornerUnit P (-A) = 1 ∧
    lowerCornerUnit P A₁ * lowerCornerUnit P A₂ =
        lowerCornerUnit P (A₁ + A₂) ∧
    lowerCornerUnit P C * lowerCornerUnit P (-C) = 1 ∧
    logisticBitPlus P A C + logisticBitMinus P A C = 1 ∧
    logisticBitVariance P A C =
      -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) := by
  have hLog := logistic_bit_variance_and_defect_equivalence hP A C
  refine ⟨?_, ?_, ?_, ?_, hLog.1, hLog.2.2.2⟩
  · unfold upperCornerUnit
    rw [conePlus_add]
    peirce_nf hP
  · unfold upperCornerUnit
    rw [conePlus_neg]
    peirce_nf hP
  · unfold lowerCornerUnit
    rw [coneMinus_add]
    peirce_nf hP
  · unfold lowerCornerUnit
    rw [coneMinus_neg]
    peirce_nf hP

/-- Local synthesis of the ordered Σ-sandwich, modular inner derivation,
and phase-conjugated cross-corner correlations. Every factor remains an
operator in the same noncommutative ring. -/
theorem curvature_modular_correlation_laws
    {P : B} (hP : P * P = P) (A C X : B) :
    sigmaSandwichPlus P A C (conePlus P A) =
        ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A ∧
    sigmaSandwichPlus P A C (coneMinus P C) =
        ((1 - genV P A C) * (1 - genV P A C)) * coneMinus P C ∧
    sigmaSandwichMinus P A C (sigmaSandwichPlus P A C X) =
        (1 - genV P A C * genV P A C) * X *
          (1 - genV P A C * genV P A C) ∧
    modularTimeDeriv P A C (conePlus P A) =
        (2 : ℤ) • (genV P A C * conePlus P A) ∧
    modularTimeDeriv P A C (coneMinus P C) =
        -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    genJ P A C * (conePlus P A * X * coneMinus P C) * (-genJ P A C) =
        qgtMinus P A C * X * qgtMinus P A C ∧
    genJ P A C * (coneMinus P C * X * conePlus P A) * (-genJ P A C) =
        qgtPlus P A C * X * qgtPlus P A C := by
  rcases sigma_sandwich_forward_modes hP A C with ⟨hPlus, hMinus, _, _⟩
  rcases modular_time_on_cone_modes hP A C with ⟨hTimePlus, hTimeMinus⟩
  rcases phase_conjugation_transports_cross_correlations hP A C X with
    ⟨hCorrPlus, hCorrMinus⟩
  exact ⟨hPlus, hMinus, sigma_sandwich_reverse_after_forward hP A C X,
    hTimePlus, hTimeMinus, hCorrPlus, hCorrMinus⟩

/-- Source-order A98: the transcript's loxodromic maps are the two ordered
`Σ`-sandwiches. This source-facing packet combines their boundary-ray and
`(Φ,J,V,Σ)` actions with the exact forward/backward composition law. The
initial Bruhat contractions are stated by their ordered factors. -/
theorem archetype_A98_loxodromic_sigma_sandwich_and_bruhat_actions
    {P : B} (hP : P * P = P) (A C X : B) :
    (1 + conePlus P A) * (1 - coneMinus P C) * conePlus P A =
      (1 - genV P A C) * conePlus P A - qgtMinus P A C ∧
    (1 + coneMinus P C) * (1 - conePlus P A) * coneMinus P C =
      (1 - genV P A C) * coneMinus P C - qgtPlus P A C ∧
    sigmaSandwichPlus P A C (conePlus P A) =
      ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A ∧
    sigmaSandwichPlus P A C (coneMinus P C) =
      ((1 - genV P A C) * (1 - genV P A C)) * coneMinus P C ∧
    sigmaSandwichMinus P A C (conePlus P A) =
      ((1 - genV P A C) * (1 - genV P A C)) * conePlus P A ∧
    sigmaSandwichMinus P A C (coneMinus P C) =
      ((1 + genV P A C) * (1 + genV P A C)) * coneMinus P C ∧
    sigmaSandwichPlus P A C (genPhi P A C) =
      (1 + genV P A C * genV P A C) * genPhi P A C +
        (2 : ℤ) • (genV P A C * genJ P A C) ∧
    sigmaSandwichPlus P A C (genJ P A C) =
      (1 + genV P A C * genV P A C) * genJ P A C +
        (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    sigmaSandwichPlus P A C (genV P A C) =
      (1 - genV P A C * genV P A C) * genV P A C ∧
    sigmaSandwichPlus P A C (genSig P A C) =
      (1 - genV P A C * genV P A C) * genSig P A C ∧
    sigmaSandwichMinus P A C (genPhi P A C) =
      (1 + genV P A C * genV P A C) * genPhi P A C -
        (2 : ℤ) • (genV P A C * genJ P A C) ∧
    sigmaSandwichMinus P A C (genJ P A C) =
      (1 + genV P A C * genV P A C) * genJ P A C -
        (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    sigmaSandwichMinus P A C (sigmaSandwichPlus P A C X) =
      (1 - genV P A C * genV P A C) * X *
        (1 - genV P A C * genV P A C) := by
  have hForward := sigma_sandwich_forward_modes hP A C
  have hEven := sigma_sandwich_forward_even_modes hP A C
  have hReverse := sigma_sandwich_reverse_modes hP A C
  refine ⟨?_, ?_, hForward.1, hForward.2.1, hReverse.1, hReverse.2.1,
    hForward.2.2.1, hForward.2.2.2, hEven.1, hEven.2,
    hReverse.2.2.1, hReverse.2.2.2, ?_⟩
  · simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  · simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  · exact sigma_sandwich_reverse_after_forward hP A C X

/-- Source-order A99: the finite phase conjugation by `J` exchanges the two
Peirce cross-corner correlations. The inner derivation and its mode actions
are supplied by the existing modular-time owner; no analytic modular group
or state-dependent KMS condition is asserted. -/
theorem archetype_A99_modular_time_and_phase_correlation_exchange
    {P : B} (hP : P * P = P) (A C X : B) :
    modularTimeDeriv P A C X =
      connPlus P A C X - connMinus P A C X ∧
    superDerivPlus P A (superDerivMinusBar P C X) +
      superDerivMinusBar P C (superDerivPlus P A X) =
        anticomm (genV P A C) X ∧
    connV P A C (modularTimeDeriv P A C X) =
      modularTimeDeriv P A C (connV P A C X) ∧
    modularTimeDeriv P A C (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    modularTimeDeriv P A C (coneMinus P C) =
      -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
    modularTimeDeriv P A C (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genJ P A C) ∧
    modularTimeDeriv P A C (genJ P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    modularTimeDeriv P A C (genV P A C) = 0 ∧
    modularTimeDeriv P A C (genSig P A C) = 0 ∧
    genJ P A C * (conePlus P A * X * coneMinus P C) *
        (-genJ P A C) = qgtMinus P A C * X * qgtMinus P A C ∧
    genJ P A C * (coneMinus P C * X * conePlus P A) *
        (-genJ P A C) = qgtPlus P A C * X * qgtPlus P A C ∧
    genJ P A C * qgtPlus P A C * (-genJ P A C) =
      qgtMinus P A C * qgtMinus P A C ∧
    genJ P A C * qgtMinus P A C * (-genJ P A C) =
      qgtPlus P A C * qgtPlus P A C := by
  have hModes := modular_time_on_tetraktys_modes hP A C
  have hCones := modular_time_on_cone_modes hP A C
  have hCorr := phase_conjugation_transports_cross_correlations hP A C X
  have hCorrOne := phase_conjugation_transports_cross_correlations hP A C (1 : B)
  refine ⟨?_, ?_, ?_, hCones.1, hCones.2, hModes.1, hModes.2.1,
    hModes.2.2.2.2, hModes.2.2.2.1, hCorr.1, hCorr.2, ?_, ?_⟩
  · simp only [modularTimeDeriv, connPlus, connMinus,
      qgtPlus, qgtMinus, genSig, comm]
    peirce_nf hP
  · simp only [superDerivPlus, superDerivMinusBar, superDerivPlusBar,
      parityConj, invS, qgtPlus, qgtMinus, anticomm]
    peirce_nf hP
  · simp only [modularTimeDeriv, connV, connPlus, connMinus,
      qgtPlus, qgtMinus, genSig, genV, comm]
    peirce_nf hP
  · simpa [qgtPlus, qgtMinus] using hCorrOne.1
  · simpa [qgtPlus, qgtMinus] using hCorrOne.2

/-- Dependency-ordered local master theorem: discrete corner unitization feeds
the logistic defect readout; that defect is retained alongside the ordered
curvature/modular/correlation laws. This is the common-carrier synthesis of
these claims, not a claim that the unrelated numbered archetype systems are
one numbering or that an analytic Tomita--Takesaki structure is constructed. -/
theorem peirce_exponential_modular_local_master
    {P : B} (hP : P * P = P) (A₁ A₂ A C X : B) :
    (upperCornerUnit P A₁ * upperCornerUnit P A₂ =
        upperCornerUnit P (A₁ + A₂) ∧
     upperCornerUnit P A * upperCornerUnit P (-A) = 1 ∧
     lowerCornerUnit P A₁ * lowerCornerUnit P A₂ =
        lowerCornerUnit P (A₁ + A₂) ∧
     lowerCornerUnit P C * lowerCornerUnit P (-C) = 1) ∧
    logisticBitVariance P A C =
      -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    (sigmaSandwichPlus P A C (conePlus P A) =
        ((1 + genV P A C) * (1 + genV P A C)) * conePlus P A ∧
     sigmaSandwichPlus P A C (coneMinus P C) =
        ((1 - genV P A C) * (1 - genV P A C)) * coneMinus P C ∧
     sigmaSandwichMinus P A C (sigmaSandwichPlus P A C X) =
        (1 - genV P A C * genV P A C) * X *
          (1 - genV P A C * genV P A C) ∧
     modularTimeDeriv P A C (conePlus P A) =
        (2 : ℤ) • (genV P A C * conePlus P A) ∧
     modularTimeDeriv P A C (coneMinus P C) =
        -((2 : ℤ) • (genV P A C * coneMinus P C)) ∧
     genJ P A C * (conePlus P A * X * coneMinus P C) * (-genJ P A C) =
        qgtMinus P A C * X * qgtMinus P A C ∧
     genJ P A C * (coneMinus P C * X * conePlus P A) * (-genJ P A C) =
        qgtPlus P A C * X * qgtPlus P A C) := by
  rcases corner_unipotent_logistic_defect_laws hP A₁ A₂ A C with
    ⟨hGroupUpper, hInvUpper, hGroupLower, hInvLower, _, hVariance⟩
  exact ⟨⟨hGroupUpper, hInvUpper, hGroupLower, hInvLower⟩, hVariance,
    curvature_modular_correlation_laws hP A C X⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceExponentialModularSynthesis
