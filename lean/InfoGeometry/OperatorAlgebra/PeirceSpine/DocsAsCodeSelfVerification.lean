/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DocsAsCodeClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import Mathlib.Tactic.NoncommRing

/-!
# Further finite operator identities for the Docs-as-Code bridge

The four channels below are the existing homogenized Peirce maps. The names
`index`, `tables`, `architecture`, and `glossary` are organizational labels;
the results assert their exact algebraic actions, not an external portal
implementation or a metric interpretation.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The odd component of the rendered idempotent squares to the variance of
its even component, and its anticommutator with that component is itself. -/
theorem rendered_odd_component_variance {P : B} (hP : P * P = P)
    (A C : B) :
    oddGrade P (renderedRepository P A C) *
        oddGrade P (renderedRepository P A C) =
      logisticBitPlus P A C * (1 - logisticBitPlus P A C) ∧
    oddGrade P (renderedRepository P A C) *
        oddGrade P (renderedRepository P A C) =
      -idempotencyDefect (genV P A C) ∧
    logisticBitPlus P A C * oddGrade P (renderedRepository P A C) +
        oddGrade P (renderedRepository P A C) * logisticBitPlus P A C =
      oddGrade P (renderedRepository P A C) := by
  have hOdd := oddGrade_renderedRepository hP A C
  refine ⟨?_, ?_, ?_⟩
  · rw [hOdd]
    unfold logisticBitPlus genPhi qgtPlus qgtMinus conePlus coneMinus
    peirce_nf hP
  · rw [hOdd]
    unfold idempotencyDefect genPhi genV qgtMinus conePlus coneMinus
    peirce_nf hP
  · rw [hOdd]
    unfold logisticBitPlus genPhi qgtPlus qgtMinus conePlus coneMinus
    peirce_nf hP

/-- The lower-corner state commutator is exactly the difference of two
declarative updates, hence the lower-corner update of their payload difference. -/
theorem declarativeUpdate_plan_difference {P : B} (hP : P * P = P)
    (D₁ D₂ : B) :
    comm (declarativeUpdate P D₂) (declarativeUpdate P D₁) =
        declarativeUpdate P D₂ - declarativeUpdate P D₁ ∧
    comm (declarativeUpdate P D₂) (declarativeUpdate P D₁) =
        (1 - P) * (D₂ - D₁) * P := by
  unfold declarativeUpdate comm
  constructor <;> peirce_nf hP

/-- Reversing the D₄₉ commutator order gives the positive sign. Its square
is the negative metric multiplied by the logistic discriminant. -/
theorem static_live_commutator_and_square {P : B} (hP : P * P = P)
    (A C : B) :
    comm (logisticBitPlus P A C) (liveTransfer P A C) =
        (1 - (2 : ℤ) • genV P A C) * genJ P A C ∧
    comm (logisticBitPlus P A C) (liveTransfer P A C) *
        comm (logisticBitPlus P A C) (liveTransfer P A C) =
      -(1 + (4 : ℤ) • idempotencyDefect (genV P A C)) * genV P A C := by
  have hComm := liveTransfer_logistic_commutator hP A C
  have hRev : comm (logisticBitPlus P A C) (liveTransfer P A C) =
      -comm (liveTransfer P A C) (logisticBitPlus P A C) := by
    unfold comm
    noncomm_ring
  have hReverse : comm (logisticBitPlus P A C) (liveTransfer P A C) =
      (1 - (2 : ℤ) • genV P A C) * genJ P A C := by
    rw [hRev, hComm]
    abel
  constructor
  · exact hReverse
  · rw [hRev]
    simpa only [neg_mul, mul_neg, neg_neg] using
      liveTransfer_logistic_commutator_square hP A C

/-- Four channel labels inherit the full 4-by-4 spectral-selection theorem
from the existing homogenized Peirce maps. Their common scale is `8 V²`. -/
theorem docs_page_channel_selection {P : B} (hP : P * P = P)
    (A C X : B) :
    hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
        (8 : ℤ) • ((genV P A C * genV P A C) * X) ∧
    hProjV P A C (genPhi P A C) = 0 ∧
    hProjV P A C (genJ P A C) = 0 ∧
    hProjV P A C (genSig P A C) = 0 ∧
    hProjPhi P A C (genV P A C) = 0 ∧
    hProjPhi P A C (genJ P A C) = 0 ∧
    hProjPhi P A C (genSig P A C) = 0 ∧
    hProjJ P A C (genV P A C) = 0 ∧
    hProjJ P A C (genPhi P A C) = 0 ∧
    hProjJ P A C (genSig P A C) = 0 ∧
    hProjSig P A C (genV P A C) = 0 ∧
    hProjSig P A C (genPhi P A C) = 0 ∧
    hProjSig P A C (genJ P A C) = 0 := by
  rcases archetype_A13_homogenized_projectors hP A C X with
    ⟨hSum, _, hVΦ, hVJ, hVSig, _, hPhiV, hPhiJ, hPhiSig,
      _, hJV, hJSig, hJSig2, _, hSigV, hSigPhi, hSigJ⟩
  exact ⟨hSum, hVΦ, hVJ, hVSig, hPhiV, hPhiJ, hPhiSig, hJV, hJSig,
    hJSig2, hSigV, hSigPhi, hSigJ⟩

/-- The finite self-verification bundle combines the D₄₉ rendered state,
variance, declarative update law, and corrected commutator orientation. -/
theorem docs_as_code_self_verifying_bundle {P : B} (hP : P * P = P)
    (A C D₁ D₂ : B) :
    renderedRepository P A C * renderedRepository P A C =
        renderedRepository P A C ∧
    evenGrade P (renderedRepository P A C) = logisticBitPlus P A C ∧
    oddGrade P (renderedRepository P A C) * oddGrade P (renderedRepository P A C) =
        -idempotencyDefect (genV P A C) ∧
    declarativeUpdate P D₂ * declarativeUpdate P D₁ = declarativeUpdate P D₂ ∧
    comm (logisticBitPlus P A C) (liveTransfer P A C) =
        (1 - (2 : ℤ) • genV P A C) * genJ P A C := by
  exact ⟨renderedRepository_idempotent hP A C,
    evenGrade_renderedRepository hP A C,
    (rendered_odd_component_variance hP A C).2.1,
    (declarativeUpdate_overwrite hP D₁ D₂).2.1,
    (static_live_commutator_and_square hP A C).1⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
