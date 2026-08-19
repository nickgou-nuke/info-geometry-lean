import InfoGeometry.Canonical.SheetSplitQuaternionic

/-!
# Finite six-state Tomita identities

The carrier is the existing `Mat23C` matrix algebra.  Left and right
multiplication are kept as the two commuting standard-form actions, while
`star` is the finite-dimensional Tomita involution.  The statements below are
algebraic identities; no von Neumann completion or KMS assertion is made.
-/

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.FiniteKreinTomitaSixState

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev SixStateOperator := Mat23C

def leftAction (A X : SixStateOperator) : SixStateOperator := A * X

def rightAction (A X : SixStateOperator) : SixStateOperator := X * A

def tomita (X : SixStateOperator) : SixStateOperator := star X

def kreinAdjoint (beta A : SixStateOperator) : SixStateOperator :=
  beta * star A * beta

def modularAction
    (rho rhoInv X : SixStateOperator) : SixStateOperator :=
  rho * X * rhoInv

def modularActionInverse
    (rho rhoInv X : SixStateOperator) : SixStateOperator :=
  rhoInv * X * rho

theorem modularAction_inverse_left
    (rho rhoInv X : SixStateOperator)
    (h₁ : rhoInv * rho = 1) (h₂ : rho * rhoInv = 1) :
    modularActionInverse rho rhoInv (modularAction rho rhoInv X) = X := by
  unfold modularAction modularActionInverse
  calc
    rhoInv * (rho * X * rhoInv) * rho =
        (rhoInv * rho) * X * (rhoInv * rho) := by noncomm_ring
    _ = X := by rw [h₁, one_mul, mul_one]

theorem modularAction_inverse_right
    (rho rhoInv X : SixStateOperator)
    (h₁ : rhoInv * rho = 1) (h₂ : rho * rhoInv = 1) :
    modularAction rho rhoInv (modularActionInverse rho rhoInv X) = X := by
  unfold modularAction modularActionInverse
  calc
    rho * (rhoInv * X * rho) * rhoInv =
        (rho * rhoInv) * X * (rho * rhoInv) := by noncomm_ring
    _ = X := by rw [h₂, one_mul, mul_one]

@[simp] theorem modularAction_one (X : SixStateOperator) :
    modularAction (1 : SixStateOperator) 1 X = X := by
  simp [modularAction]

theorem modularAction_comp
    (rho rhoInv sigma sigmaInv X : SixStateOperator) :
    modularAction rho rhoInv (modularAction sigma sigmaInv X) =
      modularAction (rho * sigma) (sigmaInv * rhoInv) X := by
  simp [modularAction, Matrix.mul_assoc]

/-- The finite modular action is an equivalence when its inverse witnesses hold. -/
def modularActionEquiv
    (rho rhoInv : SixStateOperator)
    (h₁ : rhoInv * rho = 1) (h₂ : rho * rhoInv = 1) :
    SixStateOperator ≃ SixStateOperator where
  toFun := modularAction rho rhoInv
  invFun := modularActionInverse rho rhoInv
  left_inv := modularAction_inverse_left rho rhoInv
    (h₁ := h₁) (h₂ := h₂)
  right_inv := modularAction_inverse_right rho rhoInv
    (h₁ := h₁) (h₂ := h₂)

@[simp] theorem modularActionEquiv_apply
    (rho rhoInv : SixStateOperator)
    (h₁ : rhoInv * rho = 1) (h₂ : rho * rhoInv = 1)
    (X : SixStateOperator) :
    modularActionEquiv rho rhoInv h₁ h₂ X = modularAction rho rhoInv X := rfl

@[simp] theorem modularActionEquiv_symm_apply
    (rho rhoInv : SixStateOperator)
    (h₁ : rhoInv * rho = 1) (h₂ : rho * rhoInv = 1)
    (X : SixStateOperator) :
    (modularActionEquiv rho rhoInv h₁ h₂).symm X =
      modularActionInverse rho rhoInv X := rfl

theorem leftAction_rightAction_commute
    (A B X : SixStateOperator) :
    leftAction A (rightAction B X) =
      rightAction B (leftAction A X) := by
  simp [leftAction, rightAction, Matrix.mul_assoc]

theorem tomita_involutive (X : SixStateOperator) :
    tomita (tomita X) = X := by
  simp [tomita]

theorem tomita_leftAction
    (A X : SixStateOperator) :
    tomita (leftAction A X) = rightAction (star A) (tomita X) := by
  simp [tomita, leftAction, rightAction, star_mul]

theorem tomita_rightAction
    (A X : SixStateOperator) :
    tomita (rightAction A X) = leftAction (star A) (tomita X) := by
  simp [tomita, leftAction, rightAction, star_mul]

theorem kreinAdjoint_involutive
    (beta A : SixStateOperator)
    (hbeta_star : star beta = beta)
    (hbeta_sq : beta * beta = 1) :
    kreinAdjoint beta (kreinAdjoint beta A) = A := by
  simp [kreinAdjoint, star_mul, hbeta_star, hbeta_sq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hbeta_sq, one_mul]

theorem kreinAdjoint_mul
    (beta A B : SixStateOperator)
    (hbeta_sq : beta * beta = 1) :
    kreinAdjoint beta (A * B) =
      kreinAdjoint beta B * kreinAdjoint beta A := by
  simp only [kreinAdjoint, star_mul]
  calc
    beta * (star B * star A) * beta =
        (beta * star B) * (star A * beta) := by
          simp only [mul_assoc]
    _ = (beta * star B * beta) * (beta * star A * beta) := by
          calc
            (beta * star B) * (star A * beta) =
                beta * star B * (beta * beta) * (star A * beta) := by
                  rw [hbeta_sq]
                  simp only [mul_one, mul_assoc]
            _ = (beta * star B * beta) *
                (beta * star A * beta) := by
                  simp only [mul_assoc]

theorem tomita_kreinAdjoint_intertwines
    (beta A : SixStateOperator)
    (hbeta_star : star beta = beta) :
    tomita (kreinAdjoint beta A) =
      kreinAdjoint beta (tomita A) := by
  simp [tomita, kreinAdjoint, star_mul, hbeta_star, Matrix.mul_assoc]

theorem tomita_modularAction_inverse
    (rho rhoInv X : SixStateOperator)
    (hρ_star : star rho = rho)
    (hρInv_star : star rhoInv = rhoInv) :
    tomita (modularAction rho rhoInv X) =
      modularActionInverse rho rhoInv (tomita X) := by
  simp [tomita, modularAction, modularActionInverse, star_mul,
    hρ_star, hρInv_star, Matrix.mul_assoc]

theorem sheetGrading_squared :
    sixParity * sixParity = (1 : SixStateOperator) := by
  simpa [pow_two] using
    InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixParity_squared

theorem diracKreinSymmetry_squared :
    sixSheetExchange * sixSheetExchange = (1 : SixStateOperator) := by
  simpa [pow_two] using
    InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixSheetExchange_involutive

theorem diracKrein_symmetry_exchanges_sheets :
    sixSheetExchange * sixParity * sixSheetExchange =
      -sixParity := by
  exact InfoGeometry.Canonical.TwoSheetThreeColorWeyl.sixSheetExchange_flips_parity

theorem continuous_leftAction (A : SixStateOperator) :
    Continuous (leftAction A) := by
  unfold leftAction
  exact continuous_const.matrix_mul continuous_id

theorem continuous_rightAction (A : SixStateOperator) :
    Continuous (rightAction A) := by
  unfold rightAction
  exact continuous_id.matrix_mul continuous_const

theorem continuous_tomita :
    Continuous tomita := by
  unfold tomita
  exact ContinuousStar.continuous_star

theorem continuous_kreinAdjoint (beta : SixStateOperator) :
    Continuous (kreinAdjoint beta) := by
  unfold kreinAdjoint
  exact (continuous_const.matrix_mul ContinuousStar.continuous_star).matrix_mul
    continuous_const

theorem continuous_modularAction
    (rho rhoInv : SixStateOperator) :
    Continuous (modularAction rho rhoInv) := by
  unfold modularAction
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end InfoGeometry.Canonical.FiniteKreinTomitaSixState
