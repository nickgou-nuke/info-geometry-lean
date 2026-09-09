import Mathlib.Tactic

/-!
# Projective glide as a spatial supercharge

This module ties the projective-crystal `κ` mechanism to the SUSY square law:

* projective momentum glide squares to a full reciprocal translation;
* an odd supercharge squares to the Hamiltonian/translation atom;
* both instantiate the same abstract `SquareRootTranslation` pattern;
* the nilpotent limit collapses the square to zero.
-/

noncomputable section

namespace ProjectiveGlideSuperchargeUnification

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev KPoint := ℚ × ℚ

/-- Projective momentum glide with half reciprocal translation. -/
def kGlide (k : KPoint) : KPoint := (-k.1, k.2 + (1/2 : ℚ))

/-- Full reciprocal translation. -/
def fullTranslate (k : KPoint) : KPoint := (k.1, k.2 + 1)

/-- The projective glide squares to full reciprocal translation. -/
theorem kGlide_sq : kGlide (kGlide k) = fullTranslate k := by
  cases k with
  | mk kx ky =>
    simp [kGlide, fullTranslate]
    ring

/-- Bulk supercharge. -/
def Q : M2C := !![0, 1; 1, 0]

/-- Hamiltonian / even translation atom. -/
def H : M2C := 1

/-- Nilpotent limit supercharge. -/
def qNil : M2C := !![0, 1; 0, 0]

/-- Supercharge square law. -/
theorem Q_sq : Q * Q = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Q, H, Matrix.mul_apply, Fin.sum_univ_two]

/-- Super-anticommutator form. -/
theorem Q_anticomm : Q * Q + Q * Q = (2 : ℂ) • H := by
  rw [Q_sq]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [H] <;> norm_num

/-- Nilpotent square law. -/
theorem qNil_sq_zero : qNil * qNil = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qNil, Matrix.mul_apply, Fin.sum_univ_two]

/-- Abstract square-root-of-translation structure. -/
structure SquareRootTranslation where
  Carrier : Type
  op : Carrier → Carrier
  evenTranslation : Carrier → Carrier
  square_law : ∀ x, op (op x) = evenTranslation x

/-- The projective momentum glide is a square root of reciprocal translation. -/
def projectiveGlideSquareRoot : SquareRootTranslation where
  Carrier := KPoint
  op := kGlide
  evenTranslation := fullTranslate
  square_law := by intro k; exact kGlide_sq

/-- Matrix square-root law for SUSY. -/
structure MatrixSquareRootTranslation where
  odd : M2C
  evenTranslation : M2C
  square_law : odd * odd = evenTranslation

/-- The bulk supercharge is a square root of the Hamiltonian. -/
def superchargeSquareRoot : MatrixSquareRootTranslation where
  odd := Q
  evenTranslation := H
  square_law := Q_sq

/-- The nilpotent limit has zero even translation. -/
def nilpotentLimitSquareRoot : MatrixSquareRootTranslation where
  odd := qNil
  evenTranslation := 0
  square_law := qNil_sq_zero

/-- Named square law for the projective glide structure. -/
theorem projectiveGlideSquareRoot_square_law :
    ∀ x, projectiveGlideSquareRoot.op (projectiveGlideSquareRoot.op x) =
      projectiveGlideSquareRoot.evenTranslation x :=
  projectiveGlideSquareRoot.square_law

/-- Named square law for the bulk supercharge structure. -/
theorem superchargeSquareRoot_square_law :
    superchargeSquareRoot.odd * superchargeSquareRoot.odd = superchargeSquareRoot.evenTranslation :=
  superchargeSquareRoot.square_law

/-- Named square law for the nilpotent-limit structure. -/
theorem nilpotentLimitSquareRoot_square_law :
    nilpotentLimitSquareRoot.odd * nilpotentLimitSquareRoot.odd =
      nilpotentLimitSquareRoot.evenTranslation :=
  nilpotentLimitSquareRoot.square_law

end ProjectiveGlideSuperchargeUnification
