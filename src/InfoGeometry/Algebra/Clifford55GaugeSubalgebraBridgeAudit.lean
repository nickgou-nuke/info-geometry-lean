/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Clifford55GaugeSubalgebraBridge

/-!
# Audit Companion: $\mathcal{C}\ell(5,5)$ Split-Octonionic Standard Model Gauge Subalgebra Bridge

This file audits the axiomatic footprint of all theorems in
`InfoGeometry.Algebra.Clifford55GaugeSubalgebraBridge`.
-/

namespace InfoGeometry.Algebra.Clifford55GaugeSubalgebra.Audit

open InfoGeometry.Algebra.Clifford55GaugeSubalgebra

#print axioms peirce_decomposition
#print axioms stabilizes_of_comm_two
#print axioms stabilizes_iff_cross_blocks_vanish
#print axioms stabilizes_block_diagonal_sum
#print axioms block_mul_orthogonal_left
#print axioms block_mul_orthogonal_right
#print axioms block_commutator_orthogonal_12
#print axioms block_commutator_orthogonal_13
#print axioms block_commutator_orthogonal_23

#print axioms e1_mul_self
#print axioms e2_mul_self
#print axioms e3_mul_self
#print axioms e1_mul_e2
#print axioms e2_mul_e1
#print axioms e1_mul_e3
#print axioms e3_mul_e1
#print axioms e2_mul_e3
#print axioms e3_mul_e2
#print axioms e1_add_e2_add_e3
#print axioms canonicalHIdempotentSystem
#print axioms e1_trace
#print axioms e2_trace
#print axioms e3_trace
#print axioms idempotents_trace_sum

#print axioms e1_mul_metric55
#print axioms e2_mul_metric55
#print axioms e3_mul_metric55
#print axioms metric55_block_partition

#print axioms block_hyperbolicOrthogonal_e1
#print axioms block_hyperbolicOrthogonal_e2
#print axioms block_hyperbolicOrthogonal_e3
#print axioms stabilizer_commutator_stabilizes
#print axioms smStabilizerLieSubalgebra

#print axioms color_weak_commutator_zero
#print axioms color_hypercharge_commutator_zero
#print axioms weak_hypercharge_commutator_zero
#print axioms hyperchargeGenerator_hyperbolicOrthogonal
#print axioms hyperchargeGenerator_in_e3

#print axioms clifford55_standard_model_gauge_subalgebra_synthesis

/-- An off-diagonal Peirce block is square-zero by orthogonality, even in a
noncommutative ring. This is an algebraic check, not an axiom-footprint claim. -/
theorem off_diagonal_peirce_square_zero {R : Type*} [Ring R]
    (S : OrthogonalIdempotentSystem R) (X : R) :
    (S.e1 * X * S.e2) * (S.e1 * X * S.e2) = 0 := by
  calc
    (S.e1 * X * S.e2) * (S.e1 * X * S.e2) =
        S.e1 * X * (S.e2 * S.e1) * X * S.e2 := by simp only [mul_assoc]
    _ = 0 := by rw [S.e2_e1_ortho]; simp

#print axioms off_diagonal_peirce_square_zero

end InfoGeometry.Algebra.Clifford55GaugeSubalgebra.Audit
