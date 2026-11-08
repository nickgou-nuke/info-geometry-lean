/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge

/-!
# Operator shadow of a versioned documentation pipeline

The external Docs-as-Code workflow motivates this organization, but the
theorems below concern only the repository's Peirce ring and finite three-layer
operator. They do not formalize MkDocs, Jinja, SQLite, CI, or AWS.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra (third)

variable {B : Type*} [Ring B]

/-- Algebraic identities arranged in the order of a code/documentation
pipeline: complement conservation, a two-sided corner transition, a finite
three-layer path resolvent, and the two defect identities of the Peirce
transfer and logistic section. -/
theorem docs_pipeline_operator_shadow
    {P P₁ P₂ : B} (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (H A C : B) :
    comm H P + comm H (1 - P) = 0 ∧
    ((1 + conePlus P A) * (1 - coneMinus P C)) *
      ((1 + coneMinus P C) * (1 - conePlus P A)) = 1 ∧
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
      ((1 + conePlus P A) * (1 - coneMinus P C)) = 1 ∧
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C =
      P₁ * A * P₂ * C * third P₁ P₂ ∧
    twoStepUpper P₁ P₂ A C * twoStepUpper P₁ P₂ A C *
      twoStepUpper P₁ P₂ A C = 0 ∧
    (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
    twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C) = 1 ∧
    idempotencyDefect (P + genPhi P A C) = genV P A C ∧
    ((2 : ℤ) • (P + genPhi P A C) - 1) *
      ((2 : ℤ) • (P + genPhi P A C) - 1) =
        1 + (4 : ℤ) • genV P A C ∧
    logisticBitPlus P A C = P - genSig P A C ∧
    idempotencyDefect (logisticBitPlus P A C) =
      idempotencyDefect (idempotencyDefect (P + genPhi P A C)) := by
  have hPlusNil : conePlus P A * conePlus P A = 0 :=
    conePlus_mul_conePlus hP A A
  have hMinusNil : coneMinus P C * coneMinus P C = 0 :=
    coneMinus_mul_coneMinus hP C C
  have hPlusUnit : (1 + conePlus P A) * (1 - conePlus P A) = 1 := by
    noncomm_ring [hPlusNil]
  have hMinusUnit : (1 - coneMinus P C) * (1 + coneMinus P C) = 1 := by
    noncomm_ring [hMinusNil]
  have hBridgeLeft :
      ((1 + conePlus P A) * (1 - coneMinus P C)) *
        ((1 + coneMinus P C) * (1 - conePlus P A)) = 1 := by
    calc
      (1 + conePlus P A) * (1 - coneMinus P C) *
          ((1 + coneMinus P C) * (1 - conePlus P A)) =
        (1 + conePlus P A) * ((1 - coneMinus P C) * (1 + coneMinus P C)) *
          (1 - conePlus P A) := by noncomm_ring
      _ = (1 + conePlus P A) * 1 * (1 - conePlus P A) := by rw [hMinusUnit]
      _ = 1 := by rw [mul_one, hPlusUnit]
  have hBridgeRight :
      ((1 + coneMinus P C) * (1 - conePlus P A)) *
        ((1 + conePlus P A) * (1 - coneMinus P C)) = 1 := by
    have hPlusUnit' : (1 - conePlus P A) * (1 + conePlus P A) = 1 := by
      noncomm_ring [hPlusNil]
    have hMinusUnit' : (1 + coneMinus P C) * (1 - coneMinus P C) = 1 := by
      noncomm_ring [hMinusNil]
    calc
      (1 + coneMinus P C) * (1 - conePlus P A) *
          ((1 + conePlus P A) * (1 - coneMinus P C)) =
        (1 + coneMinus P C) * ((1 - conePlus P A) * (1 + conePlus P A)) *
          (1 - coneMinus P C) := by noncomm_ring
      _ = (1 + coneMinus P C) * 1 * (1 - coneMinus P C) := by rw [hPlusUnit']
      _ = 1 := by rw [mul_one, hMinusUnit']
  rcases three_layer_poset_resolvent h1 h2 h12 h21 A C with
    ⟨hPath, hCube, hResolventL, hResolventR⟩
  rcases golden_coagulation_discriminant P hP A C with ⟨hGoldenDefect, hGoldenSquare⟩
  rcases rubedo_logistic_stone hP A C with
    ⟨hLogistic, _, _, _, hLogisticDefect⟩
  exact ⟨by unfold comm; noncomm_ring,
    hBridgeLeft, hBridgeRight, hPath, hCube, hResolventL, hResolventR,
    hGoldenDefect, hGoldenSquare, hLogistic, hLogisticDefect⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
