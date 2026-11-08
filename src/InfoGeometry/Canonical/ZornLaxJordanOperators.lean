import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornMatrix

namespace InfoGeometry.Canonical.ZornLaxJordanOperators

noncomputable section

/- The deleted facade used `ZornMatrix` as an endomorphism carrier, but that
   structure intentionally exposes only coordinate operations (not an additive
   group/module instance).  The operator laws therefore live canonically on
   any real module; Zorn coordinates may be represented in such a module when
   an operator model is supplied. -/
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev EndZorn (E : Type*) [AddCommGroup E] [Module ℝ E] := Module.End ℝ E

def laxBracket (H Z : EndZorn E) : EndZorn E := H * Z - Z * H

def jordanAction (S Z : EndZorn E) : EndZorn E := S * Z + Z * S

def metriplecticAction (gamma : ℝ) (H S Z : EndZorn E) : EndZorn E :=
  laxBracket H Z + gamma • jordanAction S Z

theorem laxBracket_antisymm (H Z : EndZorn E) :
    laxBracket H Z = -laxBracket Z H := by
  unfold laxBracket
  noncomm_ring

theorem jordanAction_comm (S Z : EndZorn E) :
    jordanAction S Z = jordanAction Z S := by
  unfold jordanAction
  abel

theorem laxBracket_add_left (H K Z : EndZorn E) :
    laxBracket (H + K) Z = laxBracket H Z + laxBracket K Z := by
  unfold laxBracket
  noncomm_ring

theorem laxBracket_add_right (H Z W : EndZorn E) :
    laxBracket H (Z + W) = laxBracket H Z + laxBracket H W := by
  unfold laxBracket
  noncomm_ring

theorem laxBracket_jacobi (H K Z : EndZorn E) :
    laxBracket H (laxBracket K Z) - laxBracket K (laxBracket H Z) =
      laxBracket (laxBracket H K) Z := by
  unfold laxBracket
  noncomm_ring

theorem jordanAction_add_left (S T Z : EndZorn E) :
    jordanAction (S + T) Z = jordanAction S Z + jordanAction T Z := by
  unfold jordanAction
  noncomm_ring

theorem jordanAction_add_right (S Z W : EndZorn E) :
    jordanAction S (Z + W) = jordanAction S Z + jordanAction S W := by
  unfold jordanAction
  noncomm_ring

theorem metriplecticAction_eq (gamma : ℝ) (H S Z : EndZorn E) :
    metriplecticAction gamma H S Z =
      (H * Z - Z * H) + gamma • (S * Z + Z * S) := by
  rfl

end
end InfoGeometry.Canonical.ZornLaxJordanOperators
