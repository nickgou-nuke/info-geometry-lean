import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Factor-stratified de Rham certificate shell

This file records the currently observed external audit surface for
`f = q(a) q(b) q(a-b)` in ambient dimension `8`.

It is theorem-honest:
- the Singular/Macaulay2 outputs are stored as plain data;
- arithmetic consequences of that data are proved in Lean;
- de Rham closure is *not* claimed unless the external lanes actually return it.
-/

namespace InfoGeometry.Projective.FactorStratifiedDeRhamCertificate

open Polynomial

/-! ## Exact arithmetic shadows of the verified external packets -/

/-- The exact quadratic Bernstein-Sato polynomial observed for each individual factor. -/
noncomputable def factorBernsteinPoly : ℤ[X] := X ^ 2 + 3 * X + 2

/-- The exact cubic Bernstein-Sato polynomial observed for the three-factor ideal. -/
noncomputable def generalBernsteinPoly : ℤ[X] := X ^ 3 + 10 * X ^ 2 + 33 * X + 36

/-- The exact finite-field complement count polynomial recorded by the audit. -/
def complementCountPoly (p : ℤ) : ℤ :=
  p ^ 8 - 3 * p ^ 7 + 7 * p ^ 5 - 4 * p ^ 4 - 4 * p ^ 3 + 3 * p ^ 2

theorem factorBernsteinPoly_factorization :
    factorBernsteinPoly = (X + 1) * (X + 2) := by
  simp [factorBernsteinPoly]
  ring

theorem generalBernsteinPoly_factorization :
    generalBernsteinPoly = (X + 3) ^ 2 * (X + 4) := by
  simp [generalBernsteinPoly]
  ring

theorem factorBernsteinPoly_eval_neg_one :
    eval (-1) factorBernsteinPoly = 0 := by
  rw [factorBernsteinPoly_factorization]
  simp

theorem factorBernsteinPoly_eval_neg_two :
    eval (-2) factorBernsteinPoly = 0 := by
  rw [factorBernsteinPoly_factorization]
  simp

theorem generalBernsteinPoly_eval_neg_three :
    eval (-3) generalBernsteinPoly = 0 := by
  rw [generalBernsteinPoly_factorization]
  simp

theorem generalBernsteinPoly_eval_neg_four :
    eval (-4) generalBernsteinPoly = 0 := by
  rw [generalBernsteinPoly_factorization]
  simp

theorem complementCountPoly_factorization (p : ℤ) :
    complementCountPoly p =
      p ^ 2 * (p - 1) ^ 2 * (p + 1) * (p ^ 3 - 2 * p ^ 2 - p + 3) := by
  unfold complementCountPoly
  ring

theorem complementCountPoly_at_three :
    complementCountPoly 3 = 1296 := by
  norm_num [complementCountPoly]

theorem complementCountPoly_at_five :
    complementCountPoly 5 = 175200 := by
  norm_num [complementCountPoly]

theorem complementCountPoly_at_seven :
    complementCountPoly 7 = 3400992 := by
  norm_num [complementCountPoly]

/-! ## Direct finite-stratum arithmetic

The bounded external computation is not represented as a certificate or a
status-bearing witness.  Its finite numerical content is stated directly;
analytic de Rham closure remains a separate theorem frontier.
-/

def ambientDimension : ℕ := 8
def pairIntersectionDimension : ℕ := 6
def tripleIntersectionDimension : ℕ := 5
def singularLocusDimension : ℕ := 6

def pairCodimension : ℕ := ambientDimension - pairIntersectionDimension
def tripleCodimension : ℕ := ambientDimension - tripleIntersectionDimension
def singularLocusCodimension : ℕ := ambientDimension - singularLocusDimension

theorem pairCodimension_eq_two : pairCodimension = 2 := by
  rfl

theorem tripleCodimension_eq_three : tripleCodimension = 3 := by
  rfl

theorem singularLocusCodimension_eq_two : singularLocusCodimension = 2 := by
  rfl

end InfoGeometry.Projective.FactorStratifiedDeRhamCertificate
