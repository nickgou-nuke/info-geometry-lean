/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Nontriviality

/-!
# Polynomial evaluation determinants and their Vandermonde factor

For arbitrary polynomial columns `p j`, reduce each column modulo the monic
node polynomial `∏ i, (X - C (v i))`. The remainders retain their evaluations
at every node and have degree less than the number of nodes. Their coefficient
matrix therefore gives an exact factorization of the evaluation matrix through
the native Vandermonde matrix.

Specializing the nodes to independent `MvPolynomial` variables and the columns
to arbitrary monomials constructs a polynomial quotient for every determinant
alternant. No distinct-node hypothesis is used to construct this quotient.
This establishes polynomial divisibility of alternants; it does not identify
the quotient with a representation character or classify arbitrary alternating
multivariate polynomials.
-/

noncomputable section

open scoped BigOperators
open Polynomial

namespace InfoGeometry.Algebra.PolynomialAlternantDivisibility

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The monic polynomial that vanishes at every evaluation node, with
multiplicity retained when nodes coincide. -/
def nodePolynomial (v : Fin n → R) : R[X] :=
  ∏ i : Fin n, (X - C (v i))

/-- Coefficients of the polynomial columns after division by the monic node
polynomial. Rows index powers and columns retain the input column order. -/
def remainderCoefficientMatrix (v : Fin n → R) (p : Fin n → R[X]) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => (p j %ₘ nodePolynomial v).coeff i

theorem nodePolynomial_monic (v : Fin n → R) : (nodePolynomial v).Monic := by
  exact Polynomial.monic_prod_of_monic Finset.univ
    (fun i : Fin n => X - C (v i)) (fun i _ => Polynomial.monic_X_sub_C (v i))

theorem nodePolynomial_natDegree [Nontrivial R] (v : Fin n → R) :
    (nodePolynomial v).natDegree = n := by
  simp [nodePolynomial, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]

theorem nodePolynomial_degree [Nontrivial R] (v : Fin n → R) :
    (nodePolynomial v).degree = (n : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (nodePolynomial_monic v).ne_zero,
    nodePolynomial_natDegree]

theorem nodePolynomial_eval (v : Fin n → R) (i : Fin n) :
    (nodePolynomial v).eval (v i) = 0 := by
  unfold nodePolynomial
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Monic remainders preserve all prescribed node evaluations. -/
theorem remainder_eval (v : Fin n → R) (p : R[X]) (i : Fin n) :
    (p %ₘ nodePolynomial v).eval (v i) = p.eval (v i) := by
  exact Polynomial.eval₂_modByMonic_eq_self_of_root
    (f := RingHom.id R) (p := p) (nodePolynomial_eval v i)

theorem remainder_degree_lt [Nontrivial R] (v : Fin n → R) (p : R[X]) :
    (p %ₘ nodePolynomial v).degree < (n : WithBot ℕ) := by
  simpa only [nodePolynomial_degree] using
    Polynomial.degree_modByMonic_lt p (nodePolynomial_monic v)

/-- Exact factorization of the full evaluation matrix, with no degree bound
on the original columns and no invertibility or distinctness assumption. -/
theorem polynomialEvaluation_factorization (v : Fin n → R) (p : Fin n → R[X]) :
    (fun i j => (p j).eval (v i)) =
      Matrix.vandermonde v * remainderCoefficientMatrix v p := by
  rcases subsingleton_or_nontrivial R with h | h
  · let _ := h
    funext i j
    exact Subsingleton.elim _ _
  · let _ := h
    ext i j
    simp only [Matrix.mul_apply, Matrix.vandermonde_apply, remainderCoefficientMatrix]
    rw [← remainder_eval v (p j) i, Polynomial.eval_eq_sum]
    symm
    calc
      (∑ k : Fin n, v i ^ (k : ℕ) * (p j %ₘ nodePolynomial v).coeff k) =
          ∑ k : Fin n, (p j %ₘ nodePolynomial v).coeff k * v i ^ (k : ℕ) := by
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      _ = (p j %ₘ nodePolynomial v).sum (fun k c => c * v i ^ k) :=
        Polynomial.sum_fin (fun k c => c * v i ^ k) (fun k => zero_mul _)
          (remainder_degree_lt v (p j))

/-- The determinant quotient is the determinant of an explicitly constructed
coefficient matrix, including on the collision locus. -/
theorem polynomialEvaluation_det_eq (v : Fin n → R) (p : Fin n → R[X]) :
    Matrix.det (fun i j => (p j).eval (v i)) =
      (Matrix.vandermonde v).det * (remainderCoefficientMatrix v p).det := by
  rw [polynomialEvaluation_factorization, Matrix.det_mul]

theorem vandermonde_det_dvd_polynomialEvaluation_det
    (v : Fin n → R) (p : Fin n → R[X]) :
    (Matrix.vandermonde v).det ∣ Matrix.det (fun i j => (p j).eval (v i)) :=
  ⟨(remainderCoefficientMatrix v p).det, polynomialEvaluation_det_eq v p⟩

/-- A constructed multivariate polynomial quotient for arbitrary monomial
exponents. No division by the Vandermonde polynomial occurs in this definition. -/
def alternantQuotient (e : Fin n → ℕ) : MvPolynomial (Fin n) R :=
  (remainderCoefficientMatrix
    (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R))
    (fun j : Fin n => (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) ^ e j)).det

/-- Every monomial determinant alternant is the native Vandermonde polynomial
times its constructed polynomial quotient. -/
theorem alternant_eq_vandermonde_mul_quotient (e : Fin n → ℕ) :
    Matrix.det (fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ e j) =
      (Matrix.vandermonde (fun i : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) R))).det * alternantQuotient (R := R) e := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, alternantQuotient] using
    polynomialEvaluation_det_eq
      (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R))
      (fun j : Fin n => (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) ^ e j)

theorem vandermonde_dvd_alternant (e : Fin n → ℕ) :
    (Matrix.vandermonde (fun i : Fin n =>
      (MvPolynomial.X i : MvPolynomial (Fin n) R))).det ∣
        Matrix.det (fun i j : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ e j) :=
  ⟨alternantQuotient (R := R) e, alternant_eq_vandermonde_mul_quotient e⟩

/-- Evaluation retains the polynomial factorization even at repeated nodes.
The quotient on the right is the evaluation of one fixed multivariate
polynomial, not a chosen pointwise quotient. -/
theorem alternantQuotient_eval_factorization (e : Fin n → ℕ) (v : Fin n → R) :
    Matrix.det (fun i j : Fin n => v i ^ e j) =
      (Matrix.vandermonde v).det * MvPolynomial.eval v (alternantQuotient (R := R) e) := by
  have h := congrArg (MvPolynomial.eval v)
    (alternant_eq_vandermonde_mul_quotient (R := R) e)
  rw [map_mul, (MvPolynomial.eval v).map_det
    (fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ e j),
    (MvPolynomial.eval v).map_det] at h
  have hcolumns : (MvPolynomial.eval v).mapMatrix
      (fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ e j) =
      (fun i j : Fin n => v i ^ e j) := by
    funext i j
    change (MvPolynomial.eval v)
      ((MvPolynomial.X i : MvPolynomial (Fin n) R) ^ e j) = v i ^ e j
    simp only [map_pow, MvPolynomial.eval_X]
  have hnodes : (MvPolynomial.eval v).mapMatrix
      (Matrix.vandermonde (fun i : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) R))) = Matrix.vandermonde v := by
    funext i j
    change (MvPolynomial.eval v)
      ((MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (j : ℕ)) = v i ^ (j : ℕ)
    simp only [map_pow, MvPolynomial.eval_X]
  rw [hcolumns, hnodes] at h
  exact h

end InfoGeometry.Algebra.PolynomialAlternantDivisibility
