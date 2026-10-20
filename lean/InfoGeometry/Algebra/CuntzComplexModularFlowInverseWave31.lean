/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexModularFlowClosureWave26

noncomputable section

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Algebra.CuntzComplexModularFlowClosureWave26

namespace InfoGeometry.Algebra.CuntzComplexModularFlowInverseWave31

/-- Complex modular flow at opposite times are mutually inverse on the Cuntz quotient. -/
theorem sigmaComplex_neg_left_inverse
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) (x : CuntzAlg n) :
    sigmaComplex n primes (-z) (sigmaComplex n primes z x) = x := by
  have h := congrArg (fun f : CuntzAlg n →ₐ[ℂ] CuntzAlg n => f x)
    (sigmaComplex_add n primes (-z) z)
  have hz : -z + z = (0 : ℂ) := by ring
  rw [hz, sigmaComplex_zero n primes] at h
  simpa [AlgHom.comp_apply] using h.symm

/-- Complex modular flow at opposite times are mutually inverse on the Cuntz quotient. -/
theorem sigmaComplex_neg_right_inverse
    (n : ℕ) (primes : Fin n → ℕ) (z : ℂ) (x : CuntzAlg n) :
    sigmaComplex n primes z (sigmaComplex n primes (-z) x) = x := by
  have h := congrArg (fun f : CuntzAlg n →ₐ[ℂ] CuntzAlg n => f x)
    (sigmaComplex_add n primes z (-z))
  have hz : z + -z = (0 : ℂ) := by ring
  rw [hz, sigmaComplex_zero n primes] at h
  simpa [AlgHom.comp_apply] using h.symm

end InfoGeometry.Algebra.CuntzComplexModularFlowInverseWave31
