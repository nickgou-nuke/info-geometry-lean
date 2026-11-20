/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

/-!
# Compressed localization in a noncommutative star ring

This owner records the algebraic variance of `P * Q * P` for self-adjoint
idempotents in an arbitrary (possibly noncommutative) star ring. It is a
ring identity; it does not assert positivity or analytic uncertainty bounds.
-/

namespace InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra

variable {R : Type*} [Ring R] [StarRing R]

/-- A transform restricted by a range projection before and after the
operator-valued transform. -/
def separateLocalization (P U T : R) : R := P * U * T

/-- The two complementary range masks partition the input projection under
an isometric transform. This is an algebraic conservation law in an arbitrary
noncommutative star ring; no analytic frame or positivity claim is made. -/
theorem separateLocalization_pore_conservation
    {P U T : R} (hU : star U * U = 1)
    (hT_idem : T * T = T) (hT_sa : star T = T)
    (hP_idem : P * P = P) (hP_sa : star P = P) :
    star (separateLocalization P U T) * separateLocalization P U T +
      star (separateLocalization (1 - P) U T) * separateLocalization (1 - P) U T = T := by
  have hcomp : P * P + (1 - P) * (1 - P) = 1 := by
    calc
      P * P + (1 - P) * (1 - P) = P + (1 - P) := by
        calc
          P * P + (1 - P) * (1 - P) = P + (1 - P) * (1 - P) := by rw [hP_idem]
          _ = P + (1 - P) := by
            congr 1
            calc
              (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
              _ = 1 - P := by rw [hP_idem]; noncomm_ring
      _ = 1 := by noncomm_ring
  simp only [separateLocalization, star_mul, star_sub, star_one, hT_sa, hP_sa]
  calc
    T * (star U * P) * (P * U * T) +
        T * (star U * (1 - P)) * ((1 - P) * U * T) =
          T * star U * (P * P + (1 - P) * (1 - P)) * U * T := by noncomm_ring
    _ = T * star U * 1 * U * T := by rw [hcomp]
    _ = T * (star U * U) * T := by noncomm_ring
    _ = T * T := by rw [hU]; simp
    _ = T := hT_idem

/-- Compression of `Q` to the idempotent corner determined by `P`. -/
def compressedLocalization (P Q : R) : R := P * Q * P

/-- The idempotency defect of `P * Q * P` is exactly the algebraic leakage
through the complementary idempotent `1 - P`. -/
theorem compressedLocalization_variance_eq_pore_leakage
    {P Q : R} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    compressedLocalization P Q - compressedLocalization P Q * compressedLocalization P Q =
      star ((1 - P) * Q * P) * ((1 - P) * Q * P) := by
  dsimp [compressedLocalization]
  have hcomp : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP_idem]; noncomm_ring
  have hfactor : P * Q * P - P * Q * P * (P * Q * P) = P * Q * (1 - P) * Q * P := by
    calc
      P * Q * P - P * Q * P * (P * Q * P)
          = P * Q * P - P * Q * (P * P) * Q * P := by
              congr 1
              noncomm_ring
      _ = P * Q * P - P * Q * P * Q * P := by
            rw [hP_idem]
      _ = P * (Q * Q) * P - P * Q * P * Q * P := by
            rw [hQ_idem]
      _ = P * Q * (1 - P) * Q * P := by noncomm_ring
  calc
    P * Q * P - P * Q * P * (P * Q * P) = P * Q * (1 - P) * Q * P := hfactor
    _ = P * Q * ((1 - P) * (1 - P)) * Q * P := by rw [hcomp]
    _ = star ((1 - P) * Q * P) * ((1 - P) * Q * P) := by
      simp [star_mul, hP_sa, hQ_sa]
      noncomm_ring

/-- The same compression defect is the compressed square of the associative
Lie commutator. Self-adjointness is stated explicitly; no commutativity of `R`
is assumed. -/
theorem compressedLocalization_variance_eq_commutator
    {P Q : R} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    compressedLocalization P Q - compressedLocalization P Q * compressedLocalization P Q =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
  have hcomm : ⁅P, Q⁆ * P = -((1 - P) * Q * P) := by
    rw [Ring.lie_def]
    calc
      (P * Q - Q * P) * P = P * Q * P - Q * (P * P) := by noncomm_ring
      _ = P * Q * P - Q * P := by rw [hP_idem]
      _ = -((1 - P) * Q * P) := by noncomm_ring
  have hstar : P * star ⁅P, Q⁆ = -star ((1 - P) * Q * P) := by
    calc
      P * star ⁅P, Q⁆ = star (⁅P, Q⁆ * P) := by simp [star_mul, hP_sa]
      _ = -star ((1 - P) * Q * P) := by rw [hcomm, star_neg]
  rw [hcomm, hstar, neg_mul_neg]
  exact compressedLocalization_variance_eq_pore_leakage hP_idem hP_sa hQ_idem hQ_sa

end InfoGeometry.OperatorAlgebra.KnutsenGaborOperatorAlgebra
