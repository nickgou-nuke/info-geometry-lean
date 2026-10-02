import InfoGeometry.Algebra.CyclotomicOperatorProjectors
import Mathlib.Algebra.Regular.Defs

namespace InfoGeometry.CyclotomicSplitting

open Finset
open InfoGeometry.Algebra.CyclotomicOperatorProjectors

section Cancellation

variable {Carrier : Type*} [Ring Carrier]

theorem cyclotomic_sum_vanishing_of_regular (order : ℕ) (root : Carrier)
    (periodic : root ^ order = 1) (regular : IsLeftRegular (1 - root)) :
    ∑ index ∈ range order, root ^ index = 0 := by
  apply regular
  simpa using root_of_unity_geometric_sum_annihilates periodic

theorem cyclotomic_sum_vanishing [NoZeroDivisors Carrier]
    (order : ℕ) (root : Carrier) (periodic : root ^ order = 1)
    (nontrivial : root ≠ 1) :
    ∑ index ∈ range order, root ^ index = 0 := by
  exact (mul_eq_zero.mp (root_of_unity_geometric_sum_annihilates periodic)).resolve_left
    (sub_ne_zero.mpr nontrivial.symm)

theorem triangular_root_identity [NoZeroDivisors Carrier]
    (root : Carrier) (periodic : root ^ 3 = 1) (nontrivial : root ≠ 1) :
    root ^ 2 + root + 1 = 0 := by
  have balanced := cyclotomic_sum_vanishing 3 root periodic nontrivial
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using balanced

theorem idempotent_eq_zero_or_one [NoZeroDivisors Carrier]
    (projector : Carrier) (idempotent : projector * projector = projector) :
    projector = 0 ∨ projector = 1 := by
  have annihilates : projector * (projector - 1) = 0 := by
    rw [mul_sub, idempotent, mul_one, sub_self]
  exact (mul_eq_zero.mp annihilates).imp_right sub_eq_zero.mp

end Cancellation

section Normalization

variable {Scalar : Type*} [Field Scalar]

def normalizedPhase (order index : ℕ) (root : Scalar) : Scalar :=
  (order : Scalar)⁻¹ * root ^ index

theorem normalizedPhase_sum_vanishing (order : ℕ) (root : Scalar)
    (periodic : root ^ order = 1) (nontrivial : root ≠ 1) :
    ∑ index ∈ range order, normalizedPhase order index root = 0 := by
  simp only [normalizedPhase, ← Finset.mul_sum]
  rw [cyclotomic_sum_vanishing order root periodic nontrivial, mul_zero]

theorem normalizedPhase_total (order : ℕ) (root : Scalar)
    (regular : (order : Scalar) ≠ 0) :
    (order : Scalar) * normalizedPhase order 0 root = 1 := by
  simp [normalizedPhase, regular]

theorem normalizedPhase_not_idempotent :
    normalizedPhase 2 0 (-1 : ℚ) * normalizedPhase 2 0 (-1 : ℚ) ≠
      normalizedPhase 2 0 (-1 : ℚ) := by
  norm_num [normalizedPhase]

end Normalization

end InfoGeometry.CyclotomicSplitting
