/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.AnticommutingBalance
import InfoGeometry.Dynamics.CyclicRotatingProfile
import InfoGeometry.Physics.CrankingParity
import InfoGeometry.Canonical.Cl11ZornActionSeparation
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Physics.AlgebraicSymmetrySynthesisTests

open InfoGeometry.Algebra.AnticommutingBalance
open InfoGeometry.Dynamics.CyclicRotatingProfile
open InfoGeometry.Physics.CrankingParity
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.Cl11ZornActionSeparation

theorem matrix_balanced_square_nonzero :
    ((1 / 2 : ℝ) • Eplus + (1 / 2 : ℝ) • J1) ^ 2 ≠ 0 := by
  apply balanced_square_ne_zero
  · rw [implementers_anticommute, neg_add_cancel]
  · rw [Eplus_sq, J1_sq]
  · rw [Eplus_sq]
    exact one_ne_zero

example : ((1 / 2 : ℝ) • Eplus + (1 / 2 : ℝ) • J1) ^ 2 =
    (1 / 2 : ℝ) • (1 : Mat2) := by
  rw [balanced_square Eplus J1
    (by rw [implementers_anticommute, neg_add_cancel])
    (by rw [Eplus_sq, J1_sq]), Eplus_sq]

example : Function.Periodic (rotatingProfile (harmonicProfile 3 2 1) 1 7)
    (2 * Real.pi / 3) :=
  periodic_at_each_time _ _ _ _ (harmonicProfile_periodic 3 (by norm_num) 2 1)

theorem triangular_profile_changes_in_laboratory :
    rotatingProfile (harmonicProfile 3 2 1) 1 (Real.pi / 3) 0 ≠
      rotatingProfile (harmonicProfile 3 2 1) 1 0 0 := by
  have phase : (3 : ℝ) * (0 - 1 * (Real.pi / 3)) = -Real.pi := by ring
  change 2 + 1 * Real.cos ((3 : ℝ) * (0 - 1 * (Real.pi / 3))) ≠
    2 + 1 * Real.cos ((3 : ℝ) * (0 - 1 * 0))
  rw [phase]
  norm_num

example (time angle : ℝ) :
    rotatingProfile (harmonicProfile 3 2 1) 1 time (angle + 1 * time) =
      harmonicProfile 3 2 1 angle :=
  stationary_in_rotating_frame _ _ _ _

example (angle : ℝ) : 0 < harmonicProfile 3 2 1 angle :=
  harmonicProfile_positive 3 2 1 angle (by norm_num)

example : routhian (LinearMap.id : ℝ →ₗ[ℝ] ℝ) LinearMap.id 2 1 = -1 := by
  norm_num [routhian]

inductive Archetype
  | realAlgebra
  | anticommutation
  | equalSquares
  | periodicProfile
  | rotatingCoordinates
  | commutingParity
  deriving DecidableEq

instance : Fintype Archetype where
  elems := {Archetype.realAlgebra, .anticommutation, .equalSquares,
    .periodicProfile, .rotatingCoordinates, .commutingParity}
  complete := by
    intro x
    cases x <;> simp

def balanceContext : Finset Archetype :=
  {.realAlgebra, .anticommutation, .equalSquares}

def rotationContext : Finset Archetype :=
  {.periodicProfile, .rotatingCoordinates}

def synthesisContext : Finset Archetype :=
  balanceContext ∪ rotationContext ∪ {.commutingParity}

theorem independent_branches :
    ¬ balanceContext ≤ rotationContext ∧ ¬ rotationContext ≤ balanceContext := by
  decide

theorem branch_inclusions :
    balanceContext ≤ synthesisContext ∧ rotationContext ≤ synthesisContext := by
  decide

#print axioms weighted_square
#print axioms weighted_square_of_equal_squares
#print axioms complementary_weight_identity
#print axioms complementary_weight_minimum
#print axioms complementary_weight_minimum_iff
#print axioms balanced_square
#print axioms balanced_square_ne_zero
#print axioms stationary_in_rotating_frame
#print axioms periodic_at_each_time
#print axioms time_shift
#print axioms time_derivative
#print axioms harmonicProfile_periodic
#print axioms harmonicProfile_bounds
#print axioms harmonicProfile_positive
#print axioms primitive_phases_distinct
#print axioms primitive_phase_cycle
#print axioms triangular_phase_equation
#print axioms routhian_commutes_parity
#print axioms routhian_preserves_parity_eigenvectors
#print axioms routhian_joint_eigenvector
#print axioms matrix_balanced_square_nonzero
#print axioms triangular_profile_changes_in_laboratory
#print axioms independent_branches
#print axioms branch_inclusions

/-! ### Non-Commutative Operator Realization of `AlgebraicSymmetrySynthesisTests.Archetype` over `[Ring B]` -/

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `Archetype` node to its
canonical Peirce operator in `[Ring B]`. -/
def symmetrySynthesisArchetypeOperator (P A C X : B) : Archetype → B
  | .realAlgebra => evenGrade P X + oddGrade P X
  | .anticommutation => InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm (genPhi P A C) (genJ P A C)
  | .equalSquares => genSig P A C * genSig P A C - genV P A C * genV P A C
  | .periodicProfile => derivSqPhi P A C (genJ P A C)
  | .rotatingCoordinates => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)
  | .commutingParity => InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (evenGrade P X)

/-- **Theorem (Non-Commutative Operator Identities across `AlgebraicSymmetrySynthesisTests.Archetype`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the six archetypes
satisfy Peirce completeness, anticommutation `{Φ, J} = 0`, equal Casimir squares
`Σ² - V² = 0`, double-commutator harmonic recursion, rotating-frame commutator `[Φ, J] = -2 Σ`,
and exact parity commutation `[P, evenGrade P X] = 0`. -/
theorem symmetrySynthesisArchetype_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    symmetrySynthesisArchetypeOperator P A C X .realAlgebra = X ∧
    symmetrySynthesisArchetypeOperator P A C X .anticommutation = 0 ∧
    symmetrySynthesisArchetypeOperator P A C X .equalSquares = 0 ∧
    symmetrySynthesisArchetypeOperator P A C X .periodicProfile =
      -((4 : ℤ) • (genV P A C * genJ P A C)) ∧
    symmetrySynthesisArchetypeOperator P A C X .rotatingCoordinates =
      -((2 : ℤ) • genSig P A C) ∧
    symmetrySynthesisArchetypeOperator P A C X .commutingParity = 0 := by
  dsimp only [symmetrySynthesisArchetypeOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A5_klein_hadamard_spectra_and_partition
      (P := P) hP A C X).2.2.2.1
  · exact (InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A7_so12_lie_brackets_and_cubic_inversions
      (P := P) hP A C).1
  · peirce_nf hP

end NonCommutativeOperatorRealization

end InfoGeometry.Physics.AlgebraicSymmetrySynthesisTests
