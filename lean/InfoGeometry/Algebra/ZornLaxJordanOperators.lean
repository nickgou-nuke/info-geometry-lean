import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix

namespace InfoGeometry.Algebra.ZornLaxJordanOperators

noncomputable section

abbrev EndZorn := Module.End ℝ (ZornMatrix ℝ)

/-- The associative commutator on the endomorphism carrier. -/
def laxBracket (H Z : EndZorn) : EndZorn := H * Z - Z * H

/-- The Jordan symmetrization on the endomorphism carrier. -/
def jordanAction (S Z : EndZorn) : EndZorn := S * Z + Z * S

/-- Formal metriplectic operator action; no dynamical claim is attached. -/
def metriplecticAction (gamma : ℝ) (H S Z : EndZorn) : EndZorn :=
  laxBracket H Z + gamma • jordanAction S Z

theorem laxBracket_antisymm (H Z : EndZorn) :
    laxBracket H Z = -laxBracket Z H := by
  unfold laxBracket
  noncomm_ring

theorem jordanAction_comm (S Z : EndZorn) :
    jordanAction S Z = jordanAction Z S := by
  unfold jordanAction
  abel

theorem laxBracket_add_left (H K Z : EndZorn) :
    laxBracket (H + K) Z = laxBracket H Z + laxBracket K Z := by
  unfold laxBracket
  noncomm_ring

theorem laxBracket_add_right (H Z W : EndZorn) :
    laxBracket H (Z + W) = laxBracket H Z + laxBracket H W := by
  unfold laxBracket
  noncomm_ring

theorem laxBracket_jacobi (H K Z : EndZorn) :
    laxBracket H (laxBracket K Z) - laxBracket K (laxBracket H Z) =
      laxBracket (laxBracket H K) Z := by
  unfold laxBracket
  noncomm_ring

theorem jordanAction_add_left (S T Z : EndZorn) :
    jordanAction (S + T) Z = jordanAction S Z + jordanAction T Z := by
  unfold jordanAction
  noncomm_ring

theorem jordanAction_add_right (S Z W : EndZorn) :
    jordanAction S (Z + W) = jordanAction S Z + jordanAction S W := by
  unfold jordanAction
  noncomm_ring

theorem metriplecticAction_eq (gamma : ℝ) (H S Z : EndZorn) :
    metriplecticAction gamma H S Z =
      (H * Z - Z * H) + gamma • (S * Z + Z * S) := by
  rfl

end

end InfoGeometry.Algebra.ZornLaxJordanOperators
