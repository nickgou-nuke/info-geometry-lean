/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ZornMultiplicationOverBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- Exact coordinate anomaly of left alternativity on the test family.  The
associator defect is the ordered coefficient commutator, right-multiplied by
the test coefficient `d`; no cancellation or commutativity hypothesis is
used. -/
theorem left_alternativity_sigma_minus_two_defect_exact (a b d : A) :
    (NCZornElement.mul
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d)).sigma_minus 2 -
      (NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b)
          (NCZornElement.pureNPlus d))).sigma_minus 2 =
      (a * b - b * a) * d := by
  rw [upperTwo_square_mul_pureNPlus_sigma_minus_two,
    upperTwo_mul_upperTwo_mul_pureNPlus_sigma_minus_two]
  simp

/-- On the displayed test elements, equality in the witnessing coordinate of
left alternativity is equivalent to annihilation of the coefficient
commutator by `d`. This is a coordinate criterion, not a claim that the full
Zorn products are equal when that coordinate vanishes. -/
theorem left_alternativity_sigma_minus_two_eq_iff (a b d : A) :
    (NCZornElement.mul
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d)).sigma_minus 2 =
      (NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b)
          (NCZornElement.pureNPlus d))).sigma_minus 2 ↔
      (a * b - b * a) * d = 0 := by
  rw [upperTwo_square_mul_pureNPlus_sigma_minus_two,
    upperTwo_mul_upperTwo_mul_pureNPlus_sigma_minus_two]

private theorem ncZornElement_ext {X Y : NCZornElement A}
    (hnp : X.n_plus = Y.n_plus) (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) : X = Y := by
  cases X
  cases Y
  simp_all

/-- On the test family, the full left-alternative equation holds exactly
when the coefficient commutator annihilates `d` on the right.  The forward
direction is detected by the `sigma_minus 2` coordinate; in the reverse
direction, the defining multiplication shows that this is the only possibly
nonzero coordinate of the difference. -/
theorem left_alternativity_test_eq_iff (a b d : A) :
    NCZornElement.mul
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))
        (NCZornElement.pureNPlus d) =
      NCZornElement.mul (upperTwo a b)
        (NCZornElement.mul (upperTwo a b)
          (NCZornElement.pureNPlus d)) ↔
      (a * b - b * a) * d = 0 := by
  constructor
  · intro h
    have hCoord := congrArg (fun X : NCZornElement A => X.sigma_minus 2) h
    rw [upperTwo_square_mul_pureNPlus_sigma_minus_two,
      upperTwo_mul_upperTwo_mul_pureNPlus_sigma_minus_two] at hCoord
    exact hCoord
  · intro h
    apply ncZornElement_ext
    · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
        NCZornElement.zornDot]
    · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
        NCZornElement.zornDot]
    · funext i
      fin_cases i <;>
        simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
          NCZornElement.zornDot, NCZornElement.zornCross]
    · funext i
      fin_cases i
      · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
          NCZornElement.zornDot, NCZornElement.zornCross]
      · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
          NCZornElement.zornDot, NCZornElement.zornCross]
      · simpa [NCZornElement.mul, upperTwo, NCZornElement.pureNPlus,
          NCZornElement.zornDot, NCZornElement.zornCross, sub_eq_add_neg] using h

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

/-- The left-alternative law on the complete `upperTwo` test family is
equivalent to commutativity of the coefficient ring. The implication to
commutativity is detected by choosing the right factor `pureNPlus 1`; the
converse follows from the exact test-family criterion above. -/
theorem left_alternativity_test_family_iff_commutative :
    (∀ a b d : A,
      NCZornElement.mul
          (NCZornElement.mul (upperTwo a b) (upperTwo a b))
          (NCZornElement.pureNPlus d) =
        NCZornElement.mul (upperTwo a b)
          (NCZornElement.mul (upperTwo a b)
            (NCZornElement.pureNPlus d))) ↔
      ∀ a b : A, a * b = b * a := by
  constructor
  · intro h a b
    have hzero := (left_alternativity_test_eq_iff a b 1).mp (h a b 1)
    have hzero' : a * b - b * a = 0 := by simpa using hzero
    exact sub_eq_zero.mp hzero'
  · intro h a b d
    apply (left_alternativity_test_eq_iff a b d).mpr
    simp [h a b]

/-- If the full NC-Zorn multiplication is left alternative, its coefficient
ring must be commutative. The test family is a genuine subfamily of the
quantified law, and its exact coordinate criterion detects every coefficient
commutator by taking `d = 1`. -/
theorem leftAlternativeLaw_implies_coeff_commutative
    (hLaw : leftAlternativeLaw (A := A)) :
    ∀ a b : A, a * b = b * a := by
  apply (left_alternativity_test_family_iff_commutative (A := A)).mp
  intro a b d
  exact hLaw (upperTwo a b) (NCZornElement.pureNPlus d)

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

/-- The corresponding right-alternativity coordinate criterion is left
annihilation of the coefficient commutator by `d`. -/
theorem right_alternativity_sigma_minus_two_eq_iff (a b d : A) :
    (NCZornElement.mul
        (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
        (upperTwo a b)).sigma_minus 2 =
      (NCZornElement.mul (NCZornElement.pureNMinus d)
        (NCZornElement.mul (upperTwo a b) (upperTwo a b))).sigma_minus 2 ↔
      d * (a * b - b * a) = 0 := by
  rw [pureNMinus_mul_upperTwo_mul_upperTwo_sigma_minus_two,
    pureNMinus_mul_upperTwo_square_sigma_minus_two]
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

/-- The full right-alternative equation on the test family holds exactly when
the coefficient commutator is annihilated on the left by `d`. The `sigma_minus
2` coordinate detects necessity, and all other output coordinates vanish by
the defining multiplication. -/
theorem right_alternativity_test_eq_iff (a b d : A) :
    NCZornElement.mul
        (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
        (upperTwo a b) =
      NCZornElement.mul (NCZornElement.pureNMinus d)
        (NCZornElement.mul (upperTwo a b) (upperTwo a b)) ↔
      d * (a * b - b * a) = 0 := by
  constructor
  · intro h
    have hCoord := congrArg (fun X : NCZornElement A => X.sigma_minus 2) h
    rw [pureNMinus_mul_upperTwo_mul_upperTwo_sigma_minus_two,
      pureNMinus_mul_upperTwo_square_sigma_minus_two] at hCoord
    exact hCoord.symm
  · intro h
    apply ncZornElement_ext
    · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
        NCZornElement.zornDot]
    · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
        NCZornElement.zornDot]
    · funext i
      fin_cases i <;>
        simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
          NCZornElement.zornDot, NCZornElement.zornCross]
    · funext i
      fin_cases i
      · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
          NCZornElement.zornDot, NCZornElement.zornCross]
      · simp [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
          NCZornElement.zornDot, NCZornElement.zornCross]
      · simpa [NCZornElement.mul, upperTwo, NCZornElement.pureNMinus,
          NCZornElement.zornDot, NCZornElement.zornCross, sub_eq_add_neg] using h.symm

/-- The right-alternative law on the complete `upperTwo` test family is
equivalent to coefficient commutativity, with the same exact criterion and
the annihilator on the left. -/
theorem right_alternativity_test_family_iff_commutative :
    (∀ a b d : A,
      NCZornElement.mul
          (NCZornElement.mul (NCZornElement.pureNMinus d) (upperTwo a b))
          (upperTwo a b) =
        NCZornElement.mul (NCZornElement.pureNMinus d)
          (NCZornElement.mul (upperTwo a b) (upperTwo a b))) ↔
      ∀ a b : A, a * b = b * a := by
  constructor
  · intro h a b
    have hzero := (right_alternativity_test_eq_iff a b 1).mp (h a b 1)
    have hzero' : a * b - b * a = 0 := by simpa using hzero
    exact sub_eq_zero.mp hzero'
  · intro h a b d
    apply (right_alternativity_test_eq_iff a b d).mpr
    simp [h a b]

/-- If the full NC-Zorn multiplication is right alternative, its coefficient
ring must be commutative. The `pureNMinus` test factor detects commutators on
the left, again with no cancellation or nonzero-divisor assumption. -/
theorem rightAlternativeLaw_implies_coeff_commutative
    (hLaw : rightAlternativeLaw (A := A)) :
    ∀ a b : A, a * b = b * a := by
  apply (right_alternativity_test_family_iff_commutative (A := A)).mp
  intro a b d
  exact hLaw (NCZornElement.pureNMinus d) (upperTwo a b)

/-- Every noncommutative coefficient ring obstructs both global alternative
laws on this operator-valued Zorn multiplication. -/
theorem noncommutative_coefficients_obstruct_alternativity
    (hne : ∃ a b : A, a * b ≠ b * a) :
    ¬ leftAlternativeLaw (A := A) ∧ ¬ rightAlternativeLaw (A := A) := by
  obtain ⟨a, b, hab⟩ := hne
  constructor
  · intro hLaw
    exact hab (leftAlternativeLaw_implies_coeff_commutative hLaw a b)
  · intro hLaw
    exact hab (rightAlternativeLaw_implies_coeff_commutative hLaw a b)

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
