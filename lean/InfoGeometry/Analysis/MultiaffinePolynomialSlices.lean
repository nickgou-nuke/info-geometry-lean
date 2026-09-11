import Mathlib.Algebra.MvPolynomial.Equiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Coordinate slices of multiaffine polynomials

This file derives affine one-coordinate slices directly from the support of an
`MvPolynomial`.  The construction uses mathlib's canonical equivalence between
polynomials indexed by `Option σ` and univariate polynomials over
`MvPolynomial σ R`.
-/

noncomputable section

namespace InfoGeometry.Analysis.MultiaffinePolynomialSlices

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [DecidableEq σ]

/--
The univariate polynomial obtained by retaining coordinate `a` and evaluating
all other coordinates at `g`.
-/
def coordinateSlice
    (p : MvPolynomial σ R)
    (a : σ)
    (g : σ → R) : Polynomial R :=
  Polynomial.map (MvPolynomial.eval (fun b : {b // b ≠ a} => g b.1))
    ((MvPolynomial.optionEquivLeft R {b : σ // b ≠ a})
      ((MvPolynomial.rename (Equiv.optionSubtypeNe a).symm) p))

/-- Evaluation of the coordinate slice agrees with updating that coordinate. -/
theorem coordinateSlice_eval
    (p : MvPolynomial σ R)
    (a : σ)
    (g : σ → R)
    (x : R) :
    (coordinateSlice p a g).eval x =
      MvPolynomial.eval (Function.update g a x) p := by
  rw [coordinateSlice, ← MvPolynomial.optionEquivLeft_elim_eval,
    MvPolynomial.eval_rename]
  apply congrArg (fun h : σ → R => MvPolynomial.eval h p)
  funext i
  by_cases hia : i = a
  · subst i
    simp
  · simp [hia]

/-- Specializing all other variables cannot increase the selected degree. -/
theorem coordinateSlice_natDegree_le_degreeOf
    (p : MvPolynomial σ R)
    (a : σ)
    (g : σ → R) :
    (coordinateSlice p a g).natDegree ≤ MvPolynomial.degreeOf a p := by
  calc
    (coordinateSlice p a g).natDegree
        ≤ ((MvPolynomial.optionEquivLeft R {b : σ // b ≠ a})
            ((MvPolynomial.rename (Equiv.optionSubtypeNe a).symm) p)).natDegree :=
      Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf a p := by
      rw [← MvPolynomial.degreeOf_eq_natDegree]

/--
A support bound on every exponent gives degree at most one for every
one-coordinate specialization.
-/
theorem coordinateSlice_natDegree_le_one
    (p : MvPolynomial σ R)
    (hmulti : ∀ m ∈ p.support, ∀ i : σ, m i ≤ 1)
    (a : σ)
    (g : σ → R) :
    (coordinateSlice p a g).natDegree ≤ 1 :=
  (coordinateSlice_natDegree_le_degreeOf p a g).trans
    (MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hmulti m hm a))

/--
Every coordinate specialization of a multiaffine polynomial is an affine
function.  Its coefficients are obtained from the canonical univariate slice,
not supplied as independent evidence.
-/
theorem eval_update_affine
    (p : MvPolynomial σ R)
    (hmulti : ∀ m ∈ p.support, ∀ i : σ, m i ≤ 1)
    (a : σ)
    (g : σ → R) :
    ∃ c d : R, ∀ x : R,
      MvPolynomial.eval (Function.update g a x) p = c + d * x := by
  let q := coordinateSlice p a g
  have hq : q.natDegree ≤ 1 :=
    coordinateSlice_natDegree_le_one p hmulti a g
  rcases Polynomial.exists_eq_X_add_C_of_natDegree_le_one hq with
    ⟨d, c, hform⟩
  refine ⟨c, d, fun x => ?_⟩
  rw [← coordinateSlice_eval p a g x]
  change q.eval x = _
  rw [hform]
  simp [add_comm]

end InfoGeometry.Analysis.MultiaffinePolynomialSlices
