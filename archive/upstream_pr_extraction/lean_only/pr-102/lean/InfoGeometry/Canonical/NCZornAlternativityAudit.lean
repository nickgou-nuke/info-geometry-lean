import InfoGeometry.Physics.ZornMultiplicationOverBdG
import Mathlib.Tactic.FinCases

/-!
# Alternativity audit for the operator-valued NC-Zorn carrier

The coefficient ring is allowed to be noncommutative.  This owner deliberately
does not install a `NonUnitalNonAssocRing` instance on `NCZornElement`: it
records a concrete obstruction directly from the displayed multiplication.
-/

namespace InfoGeometry.Canonical.NCZorn

open InfoGeometry.Physics.NCG
open InfoGeometry.Physics.PalatialTwistor

variable {A : Type*} [Ring A]

/-- The left alternative law for the displayed NC-Zorn multiplication. -/
def leftAlternativeLaw : Prop :=
  ∀ x y : NCZornElement A,
    NCZornElement.mul (NCZornElement.mul x x) y =
      NCZornElement.mul x (NCZornElement.mul x y)

/-- The right alternative law for the displayed NC-Zorn multiplication. -/
def rightAlternativeLaw : Prop :=
  ∀ x y : NCZornElement A,
    NCZornElement.mul (NCZornElement.mul x y) y =
      NCZornElement.mul x (NCZornElement.mul y y)

def upperTwo (a b : A) : NCZornElement A where
  n_plus := 0
  n_minus := 0
  sigma_plus := fun i =>
    if i = 0 then a else if i = 1 then b else 0
  sigma_minus := fun _ => 0

theorem upperTwo_square_sigma_minus_two (a b : A) :
    (NCZornElement.mul (upperTwo a b) (upperTwo a b)).sigma_minus 2 =
      a * b - b * a := by
  simp [upperTwo, NCZornElement.mul, NCZornElement.zornCross]

theorem upperTwo_square_mul_pureNPlus_sigma_minus_two (a b d : A) :
    (NCZornElement.mul
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d)).sigma_minus 2 =
      (a * b - b * a) * d := by
  simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
    NCZornElement.zornDot, NCZornElement.zornCross]

theorem upperTwo_mul_upperTwo_mul_pureNPlus_sigma_minus_two (a b d : A) :
    (NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b)
          (NCZornElement.pureNPlus d))).sigma_minus 2 = 0 := by
  simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
    NCZornElement.zornDot, NCZornElement.zornCross]

theorem left_alternativity_obstruction
    {a b d : A} (h : (a * b - b * a) * d ≠ 0) :
    NCZornElement.mul
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d) ≠
      NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b)
          (NCZornElement.pureNPlus d)) := by
  intro hEq
  have hCoord := congrArg (fun X : NCZornElement A => X.sigma_minus 2) hEq
  change
    (NCZornElement.mul
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d)).sigma_minus 2 =
      (NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b)
          (NCZornElement.pureNPlus d))).sigma_minus 2 at hCoord
  rw [upperTwo_square_mul_pureNPlus_sigma_minus_two,
    upperTwo_mul_upperTwo_mul_pureNPlus_sigma_minus_two] at hCoord
  exact h hCoord

theorem pureNMinus_mul_upperTwo_square_sigma_minus_two (a b d : A) :
    (NCZornElement.mul (NCZornElement.pureNMinus d)
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))).sigma_minus 2 =
      d * (a * b - b * a) := by
  simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
    NCZornElement.zornDot, NCZornElement.zornCross]

theorem pureNMinus_mul_upperTwo_mul_upperTwo_sigma_minus_two (a b d : A) :
    (NCZornElement.mul
        (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
        (upperTwo a b)).sigma_minus 2 = 0 := by
  simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
    NCZornElement.zornDot, NCZornElement.zornCross]

theorem right_alternativity_obstruction
    {a b d : A} (h : d * (a * b - b * a) ≠ 0) :
    NCZornElement.mul
        (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
        (upperTwo a b) ≠
      NCZornElement.mul (NCZornElement.pureNMinus d)
        (NCZornElement.mul (upperTwo a b) (upperTwo a b)) := by
  intro hEq
  have hCoord := congrArg (fun X : NCZornElement A => X.sigma_minus 2) hEq
  change
    (NCZornElement.mul
        (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
        (upperTwo a b)).sigma_minus 2 =
      (NCZornElement.mul (NCZornElement.pureNMinus d)
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))).sigma_minus 2 at hCoord
  rw [pureNMinus_mul_upperTwo_mul_upperTwo_sigma_minus_two,
    pureNMinus_mul_upperTwo_square_sigma_minus_two] at hCoord
  exact h hCoord.symm

theorem bdg_left_alternativity_fails :
    let a := matrixE12
    let b := matrixE21
    let d := (1 : BdGBlockQ)
    NCZornElement.mul
          (NCZornElement.mul (upperTwo a b) (upperTwo a b))
          (NCZornElement.pureNPlus d) ≠
        NCZornElement.mul (upperTwo a b)
          (NCZornElement.mul (upperTwo a b)
            (NCZornElement.pureNPlus d)) := by
  dsimp
  apply left_alternativity_obstruction
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [matrixE12, matrixE21, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem bdg_right_alternativity_fails :
    let a := matrixE12
    let b := matrixE21
    let d := (1 : BdGBlockQ)
    NCZornElement.mul
          (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
          (upperTwo a b) ≠
        NCZornElement.mul (NCZornElement.pureNMinus d)
          (NCZornElement.mul (upperTwo a b) (upperTwo a b)) := by
  dsimp
  apply right_alternativity_obstruction
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [matrixE12, matrixE21, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The concrete BdG coefficient lift fails both alternative laws. -/
theorem bdg_alternativity_audit :
    ¬ leftAlternativeLaw (A := BdGBlockQ) ∧
      ¬ rightAlternativeLaw (A := BdGBlockQ) := by
  constructor
  · intro h
    exact bdg_left_alternativity_fails
      (h (upperTwo matrixE12 matrixE21) (NCZornElement.pureNPlus 1))
  · intro h
    exact bdg_right_alternativity_fails
      (h (NCZornElement.pureNMinus 1) (upperTwo matrixE12 matrixE21))

end InfoGeometry.Canonical.NCZorn
