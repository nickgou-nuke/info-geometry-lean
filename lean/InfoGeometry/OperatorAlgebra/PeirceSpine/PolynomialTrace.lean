/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Native polynomial evaluation under a graded cyclic trace

The positive-degree cancellation is owned by `GradedTraceMoments`. Here it is
extended to native `Polynomial.aeval`, with the surviving constant coefficient
identified exactly. The operators remain in an arbitrary noncommutative algebra.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialTrace

open Polynomial
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.GradedTraceMoments

variable {K B M : Type*} [CommRing K] [Ring B] [Algebra K B]
  [AddCommGroup M] [Module K M]

/-- The graded cyclic trace of a polynomial in the Peirce metric is exactly
its constant coefficient times the graded trace of the unit. -/
theorem cyclic_grading_aeval (τ : B →ₗ[K] M)
    (hCyc : ∀ X Y, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C : B) (F : K[X]) :
    τ (invS P * aeval (genV P A C) F) = F.coeff 0 • τ (invS P) := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG =>
      simp only [map_add, mul_add, hF, hG, coeff_add, add_smul]
  | monomial n r =>
      rw [aeval_monomial, ← Algebra.smul_def, mul_smul_comm, map_smul]
      cases n with
      | zero => simp
      | succ k =>
          have hk : τ (invS P * (genV P A C) ^ (k + 1)) = 0 :=
            cyclic_grading_metric_power_zero τ.toAddMonoidHom hCyc hP A C k
          rw [hk]
          simp

end InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialTrace
