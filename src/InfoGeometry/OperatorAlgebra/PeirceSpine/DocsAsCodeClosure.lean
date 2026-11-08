/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DocsAsCodeOperatorBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.MultiplicatioLogisticTower
import Mathlib.Tactic.NoncommRing

/-!
# D₄₉: algebraic closure identities for the Docs-as-Code operator shadow

This file extends the finite Peirce operator model. It does not formalize the
external MkDocs, Terraform, SQLite, or Jinja implementations.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The conjugate of the code-sector idempotent by the two-corner bridge. -/
def renderedRepository (P A C : B) : B :=
  ((1 + conePlus P A) * (1 - coneMinus P C)) * P *
    ((1 + coneMinus P C) * (1 - conePlus P A))

/-- The difference between the two directed schema-transfer maps. -/
def schemaDrift (P A C : B) : B :=
  coneMinus P C * P - conePlus P A * (1 - P)

/-- A lower-corner update adjoining the code-sector idempotent. -/
def declarativeUpdate (P D : B) : B := P + (1 - P) * D * P

/-- The live transfer and its diagonal logistic section. -/
def liveTransfer (P A C : B) : B := P + genPhi P A C

/-- The finite defect identity connecting the live transfer to its logistic
section. -/
theorem live_and_static_defects {P : B} (hP : P * P = P) (A C : B) :
    idempotencyDefect (liveTransfer P A C) = genV P A C ∧
    idempotencyDefect (logisticBitPlus P A C) =
      idempotencyDefect (idempotencyDefect (liveTransfer P A C)) := by
  rcases golden_coagulation_discriminant P hP A C with ⟨hLive, _⟩
  rcases rubedo_logistic_stone hP A C with ⟨_, _, _, _, hStatic⟩
  refine ⟨?_, ?_⟩
  · change idempotencyDefect (P + genPhi P A C) = genV P A C
    exact hLive
  · change idempotencyDefect (logisticBitPlus P A C) =
      idempotencyDefect (idempotencyDefect (P + genPhi P A C))
    exact hStatic

/-- The static documentation section is the depth-zero stone of the finite
Peirce defect tower, and its defect is the first metric iterate. -/
theorem static_build_is_initial_multiplicatio_stone {P : B}
    (hP : P * P = P) (A C : B) :
    logisticBitPlus P A C = multiplicatioStone 0 P A C ∧
    idempotencyDefect (logisticBitPlus P A C) =
      multiplicatioMetric 1 P A C := by
  have hStone : logisticBitPlus P A C = multiplicatioStone 0 P A C := by
    simpa [multiplicatioStone, multiplicatioCurvature,
      Function.iterate_zero_apply, genSig, comm, qgtPlus, qgtMinus] using
        (rubedo_logistic_stone hP A C).1
  refine ⟨hStone, ?_⟩
  rw [hStone]
  simpa using multiplicatio_stone_defect hP A C 0

/-- The rendered conjugate remains idempotent. -/
theorem renderedRepository_idempotent {P : B} (hP : P * P = P)
    (A C : B) :
    renderedRepository P A C * renderedRepository P A C =
      renderedRepository P A C := by
  unfold renderedRepository
  peirce_nf hP

/-- The even part of the rendered repository is the logistic section. -/
theorem evenGrade_renderedRepository {P : B} (hP : P * P = P)
    (A C : B) :
    evenGrade P (renderedRepository P A C) = logisticBitPlus P A C := by
  unfold evenGrade renderedRepository logisticBitPlus qgtPlus qgtMinus
    conePlus coneMinus
  peirce_nf hP

/-- The complementary odd part has an explicit finite expression. -/
theorem oddGrade_renderedRepository {P : B} (hP : P * P = P)
    (A C : B) :
    oddGrade P (renderedRepository P A C) =
      -genPhi P A C + conePlus P A * qgtMinus P A C := by
  unfold oddGrade renderedRepository genPhi qgtMinus conePlus coneMinus
  peirce_nf hP

/-- The schema difference is the negative directed Peirce generator. -/
theorem schemaDrift_eq_neg_genJ {P : B} (hP : P * P = P)
    (A C : B) : schemaDrift P A C = -genJ P A C := by
  unfold schemaDrift genJ conePlus coneMinus
  peirce_nf hP

/-- Its square is the negative Jordan metric. -/
theorem schemaDrift_square {P : B} (hP : P * P = P)
    (A C : B) : schemaDrift P A C * schemaDrift P A C =
      -genV P A C := by
  rw [schemaDrift_eq_neg_genJ hP]
  have hJ : genJ P A C * genJ P A C = -genV P A C := by
    peirce_nf hP
  rw [neg_mul_neg, hJ]

/-- Contract equality of the two transfer outputs forces zero drift on the
state being compared. -/
theorem schemaDrift_contract_zero {P : B} (hP : P * P = P)
    (A C X : B)
    (hContract : coneMinus P C * (P * X) =
      conePlus P A * ((1 - P) * X)) :
    schemaDrift P A C * X = 0 := by
  have hMinus : coneMinus P C * P = coneMinus P C := by
    unfold coneMinus
    peirce_nf hP
  have hPlus : conePlus P A * (1 - P) = conePlus P A := by
    unfold conePlus
    peirce_nf hP
  calc
    schemaDrift P A C * X =
        coneMinus P C * (P * X) - conePlus P A * ((1 - P) * X) := by
          unfold schemaDrift
          calc
            (coneMinus P C * P - conePlus P A * (1 - P)) * X =
                (coneMinus P C * P) * X -
                  (conePlus P A * (1 - P)) * X := by rw [sub_mul]
            _ = coneMinus P C * (P * X) -
                  conePlus P A * ((1 - P) * X) := by
                    rw [← hMinus, ← hPlus]
                    simp only [mul_assoc]
    _ = 0 := by rw [hContract, sub_self]

/-- Declarative lower-corner updates are idempotent and the newer update
absorbs an older update under composition. -/
theorem declarativeUpdate_overwrite {P : B} (hP : P * P = P)
    (D₁ D₂ : B) :
    declarativeUpdate P D₁ * declarativeUpdate P D₁ =
        declarativeUpdate P D₁ ∧
    declarativeUpdate P D₂ * declarativeUpdate P D₁ =
        declarativeUpdate P D₂ ∧
    declarativeUpdate P 0 * declarativeUpdate P D₁ = P := by
  unfold declarativeUpdate
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- With the stated commutator convention, the live/logistic commutator has
the negative of the sign proposed in the informal extraction. -/
theorem liveTransfer_logistic_commutator {P : B}
    (hP : P * P = P) (A C : B) :
    comm (liveTransfer P A C) (logisticBitPlus P A C) =
      -((1 - (2 : ℤ) • genV P A C) * genJ P A C) := by
  unfold liveTransfer
  rcases rubedo_logistic_stone hP A C with ⟨hLog, _, _, _, _⟩
  rw [hLog]
  simp only [comm]
  peirce_nf hP

/-- The square of the convention-corrected live/logistic commutator is the
negative logistic discriminant times the Peirce metric. -/
theorem liveTransfer_logistic_commutator_square {P : B}
    (hP : P * P = P) (A C : B) :
    comm (liveTransfer P A C) (logisticBitPlus P A C) *
        comm (liveTransfer P A C) (logisticBitPlus P A C) =
      -(1 + (4 : ℤ) • idempotencyDefect (genV P A C)) * genV P A C := by
  rw [liveTransfer_logistic_commutator hP A C]
  unfold idempotencyDefect
  peirce_nf hP

/-- D₄₉ synthesis: conjugation/core, schema drift, declarative overwrite, and
the convention-corrected live/logistic commutator. -/
theorem stageD49_docs_as_code_closure {P : B} (hP : P * P = P)
    (A C X D₁ D₂ : B) :
    renderedRepository P A C * renderedRepository P A C =
        renderedRepository P A C ∧
    evenGrade P (renderedRepository P A C) = logisticBitPlus P A C ∧
    oddGrade P (renderedRepository P A C) =
      -genPhi P A C + conePlus P A * qgtMinus P A C ∧
    logisticBitPlus P A C = multiplicatioStone 0 P A C ∧
    idempotencyDefect (logisticBitPlus P A C) =
      multiplicatioMetric 1 P A C ∧
    schemaDrift P A C = -genJ P A C ∧
    schemaDrift P A C * schemaDrift P A C = -genV P A C ∧
    (coneMinus P C * (P * X) = conePlus P A * ((1 - P) * X) →
      schemaDrift P A C * X = 0) ∧
    declarativeUpdate P D₂ * declarativeUpdate P D₁ =
      declarativeUpdate P D₂ ∧
    idempotencyDefect (liveTransfer P A C) = genV P A C ∧
    idempotencyDefect (logisticBitPlus P A C) =
      idempotencyDefect (idempotencyDefect (liveTransfer P A C)) ∧
    comm (liveTransfer P A C) (logisticBitPlus P A C) =
      -((1 - (2 : ℤ) • genV P A C) * genJ P A C) := by
  exact ⟨renderedRepository_idempotent hP A C,
    evenGrade_renderedRepository hP A C,
    oddGrade_renderedRepository hP A C,
    (static_build_is_initial_multiplicatio_stone hP A C).1,
    (static_build_is_initial_multiplicatio_stone hP A C).2,
    schemaDrift_eq_neg_genJ hP A C,
    schemaDrift_square hP A C,
    fun h => schemaDrift_contract_zero hP A C X h,
    (declarativeUpdate_overwrite hP D₁ D₂).2.1,
    (live_and_static_defects hP A C).1,
    (live_and_static_defects hP A C).2,
    liveTransfer_logistic_commutator hP A C⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
