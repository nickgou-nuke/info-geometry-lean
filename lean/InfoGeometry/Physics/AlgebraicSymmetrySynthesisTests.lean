import InfoGeometry.Algebra.AnticommutingBalance
import InfoGeometry.Dynamics.CyclicRotatingProfile
import InfoGeometry.Physics.CrankingParity
import InfoGeometry.Canonical.Cl11ZornActionSeparation

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
  deriving DecidableEq, Fintype

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

end InfoGeometry.Physics.AlgebraicSymmetrySynthesisTests
