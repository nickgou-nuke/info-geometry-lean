/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.FiniteSmoothedMangoldt

/-!
# Axiom and boundary audit of finite Mangoldt smoothing

The list covers every new public definition and theorem in the owner.
The examples exercise the zero boundary and a nonzero prime contribution.
The audited theorems do not assume RH or import the external announced proof.
-/

#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.harmonicMangoldtSum
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.harmonicMangoldtSum_zero
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_zero
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_one
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.harmonicMangoldtSum_succ
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.chebyshevPsiFinite_succ
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_eq_harmonic_sub_psi
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_eq_positivePart
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.harmonicMangoldtSum_nonneg
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_nonneg
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_succ_sub
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_second_difference
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_second_difference_nonneg
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_second_difference_pos_iff
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.vonMangoldtWeight_eq_mul_second_difference
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.harmonicMangoldtSum_monotone
#print axioms InfoGeometry.Arithmetic.PrimeDistributionLaw.smoothedMangoldtSum_monotone

open InfoGeometry.Arithmetic.PrimeDistributionLaw

example : smoothedMangoldtSum 2 - 2 * smoothedMangoldtSum 1 + smoothedMangoldtSum 0 = 0 := by
  simpa [vonMangoldtWeight] using smoothedMangoldtSum_second_difference 0

example : smoothedMangoldtSum 3 - 2 * smoothedMangoldtSum 2 + smoothedMangoldtSum 1 =
    Real.log 2 / 2 := by
  simpa [vonMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    using smoothedMangoldtSum_second_difference 1

example : 0 < smoothedMangoldtSum 3 - 2 * smoothedMangoldtSum 2 + smoothedMangoldtSum 1 := by
  exact (smoothedMangoldtSum_second_difference_pos_iff 1).2 Nat.prime_two.isPrimePow
