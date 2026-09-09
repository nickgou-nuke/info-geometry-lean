import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.WittenIndexSupertracePairing

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def supertraceTerm (mu_n n_pow_beta : ℝ) : ℝ :=
  (1 - mu_n) * n_pow_beta

theorem supertrace_vacuum_cancellation (beta_weight : ℝ) :
    supertraceTerm 1 beta_weight = 0 := by
  unfold supertraceTerm
  ring

theorem supertrace_prime_doubling (p_pow_beta : ℝ) :
    supertraceTerm (-1) p_pow_beta = 2 * p_pow_beta := by
  unfold supertraceTerm
  ring

theorem supertrace_square_fermion_extinction (p2_pow_beta : ℝ) :
    supertraceTerm 0 p2_pow_beta = p2_pow_beta := by
  unfold supertraceTerm
  ring

def gradedPartitionDifference (Z_B Z_F : ℝ) : ℝ :=
  Z_B - Z_F

theorem graded_partition_cancellation_at_vacuum (E_0 : ℝ) :
    gradedPartitionDifference E_0 E_0 = 0 := by
  unfold gradedPartitionDifference
  ring

end InfoGeometry.Quantum.WittenIndexSupertracePairing
