/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import InfoGeometry.Geometry.AssociativeGaugeConnection
import InfoGeometry.Algebra.CyclicMatrixCurvature

/-!
# A polynomial operator obstruction to coefficient-valued torsion

Native differentiation and multiplication by `X` act on the whole polynomial
module, with commutator equal to the identity.  With zero coefficient
Derivatives the connection curvature is therefore `1`, so the central curving
`-1` gives corrected curvature zero.  In characteristic zero this curving is
not annihilated by any nonzero natural number.

The cyclic coefficient module kills this identity commutator.  Consequently
vanishing of its cyclic image cannot, without more hypotheses, be promoted to
additive torsion of the original operator.  This says nothing about spectral
gaps or the finite-dimensional scalar multiplier cohomology theorem.

`PolynomialXPDilation` contains the complex-coordinate version in a broader
physical import corridor.  The present theorem uses the native Mathlib maps
directly over a general commutative ring and introduces no duplicate operators.
-/

noncomputable section

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

open InfoGeometry.Algebra.CyclicMatrixCurvature

variable {K : Type*} [CommRing K]

/-- The full polynomial operator commutator, with composition as multiplication. -/
theorem polynomial_derivative_mulLeft_sub :
    (Polynomial.derivative : Module.End K (Polynomial K)) *
        LinearMap.mulLeft K Polynomial.X -
      LinearMap.mulLeft K Polynomial.X *
        (Polynomial.derivative : Module.End K (Polynomial K)) = 1 := by
  apply LinearMap.ext
  intro p
  change Polynomial.derivative (Polynomial.X * p) -
    Polynomial.X * Polynomial.derivative p = p
  simp [Polynomial.derivative_mul]

/-- Zero coefficient derivatives satisfy the required associative Leibniz law. -/
theorem polynomialOperator_zero_isLeibniz :
    IsLeibniz (0 : Module.End K (Module.End K (Polynomial K))) := by
  intro a b
  simp

/-- This local curvature is the identity operator on every polynomial. -/
theorem polynomial_curvature_eq_one :
    curvature (0 : Module.End K (Module.End K (Polynomial K))) 0
      Polynomial.derivative (LinearMap.mulLeft K Polynomial.X) = 1 := by
  simpa only [curvature, LinearMap.zero_apply, sub_zero, zero_add] using
    (polynomial_derivative_mulLeft_sub (K := K))

/-- The prescribed central curving `-1` cancels the operator curvature. -/
theorem polynomial_corrected_curvature_zero :
    curvature (0 : Module.End K (Module.End K (Polynomial K))) 0
      Polynomial.derivative (LinearMap.mulLeft K Polynomial.X) +
        (-1 : Module.End K (Polynomial K)) = 0 := by
  rw [polynomial_curvature_eq_one, add_neg_cancel]

/-- The curving is central in the full polynomial endomorphism ring. -/
theorem polynomial_curving_commute (T : Module.End K (Polynomial K)) :
    Commute (-1 : Module.End K (Polynomial K)) T := by
  show (-1 : Module.End K (Polynomial K)) * T = T * (-1)
  apply LinearMap.ext
  intro p
  change -(T p) = T (-p)
  exact (map_neg T p).symm

/-- In characteristic zero the curving has no positive additive annihilator.
The proof evaluates the operator at `1` and reads its constant coefficient. -/
theorem polynomial_curving_nsmul_ne_zero [CharZero K] (n : ℕ) (hn : n ≠ 0) :
    n • (-1 : Module.End K (Polynomial K)) ≠ 0 := by
  intro h
  have hp := LinearMap.congr_fun h (1 : Polynomial K)
  have hc := congrArg (fun p : Polynomial K => p.coeff 0) hp
  have hnK : (n : K) = 0 := by
    simpa using hc
  exact hn (Nat.cast_eq_zero.mp hnK)

/-- The identity is already a commutator in this operator algebra, so its
class in the existing cyclic coefficient module is zero. -/
theorem polynomial_cyclicClass_one :
    cyclicClass K (Module.End K (Polynomial K)) 1 = 0 := by
  rw [← polynomial_derivative_mulLeft_sub (K := K)]
  exact cyclicClass_commutator K (Module.End K (Polynomial K))
    Polynomial.derivative (LinearMap.mulLeft K Polynomial.X)

/-- Cyclic vanishing of the curving does not imply torsion of that operator. -/
theorem polynomial_cyclicClass_curving :
    cyclicClass K (Module.End K (Polynomial K)) (-1) = 0 := by
  rw [map_neg, polynomial_cyclicClass_one, neg_zero]

end InfoGeometry.Geometry.AssociativeGaugeConnection
