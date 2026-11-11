/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceHadamardNative
import InfoGeometry.Twistor.TwistorConstituentKinematics

/-!
# Twistor invariant separation and native Hadamard audit

This file checks the added declarations' axiom dependencies and two boundaries
of the intake: the mass invariant is the infinity pairing, and a count bound
requires an explicit base case and recurrence. It does not define a missing
`metricCount` or an unspecified `θΩ`.
-/

open InfoGeometry.Twistor
open PenroseIncidence TwistorKinematicTensor TwistorConstituentKinematics

-- Reuse the existing determinant theorem at the precise infinity-pairing type.
example (Z W : Twistor4) :
    (momentum Z + momentum W).det =
      (Complex.normSq (InfinityTwistor.infinityTwistor Z W) : ℂ) :=
  pairMomentum_determinant Z W

-- Conditional induction only: no unprovided metric-count recurrence is assumed
-- to describe the source's geometric objects.
example (count : ℕ → ℕ)
    (h0 : count 0 ≤ 1)
    (hstep : ∀ k, count (k + 1) ≤ 4 * count k)
    (k : ℕ) : count k ≤ 4 ^ k := by
  induction k with
  | zero =>
      simpa only [Nat.pow_zero] using h0
  | succ k ih =>
      calc
        count (k + 1) ≤ 4 * count k := hstep k
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (k + 1) := Nat.pow_add_one'.symm

#print axioms PerjesConventions.wittGram_determinant
#print axioms PerjesConventions.wittGram_determinant_of_null
#print axioms TwistorKinematicTensor.infinityConjugate_not_idempotent
#print axioms TwistorConstituentKinematics.null_twistors_witt_orthogonal_positive_mass
#print axioms TwistorConstituentKinematics.null_twistors_witt_pairing_I_zero_mass

open InfoGeometry.OperatorAlgebra.PeirceHadamardNative

#print axioms mat2EquivMatrix
#print axioms InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness.matrix_units_noncommute_of_nontrivial
#print axioms walsh
#print axioms walsh_eq
#print axioms walsh_square
#print axioms walsh_diagonal
#print axioms walsh_matrix
#print axioms walshUnit
#print axioms walshUnit_similarity
#print axioms walsh_leftRight
