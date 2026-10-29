/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SignedTransportMetric
import InfoGeometry.OperatorAlgebra.PeirceBoundaryWitness

/-! # Nondiagonal real regressions for the signed transport

Reuse the dense 4x4 square-zero arrow and nondiagonal projector from the parent.
Neither the matrix algebra nor the induced 16-dimensional endomorphism algebra
is replaced by scalar eigenvalues or a simultaneous diagonalization.
-/

namespace InfoGeometry.OperatorAlgebra.SignedTransportWitness

open Matrix InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.OperatorAlgebra.PeirceBoundaryWitness

noncomputable section

theorem arrow_nonzero : q ≠ 0 := by
  intro h
  have he := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 0) h
  norm_num [q] at he

theorem signed_transport_nonzero : skewTransport ℝ q r ≠ 0 := by
  intro h
  have he := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f 1 0 0) h
  change skewTransport ℝ q r 1 0 0 = 0 at he
  rw [skewTransport_one] at he
  norm_num [q, r, mul_apply, Fin.sum_univ_succ] at he

/-- Even for transpose-paired arrows, the signed transport is not positive. -/
theorem signed_positive_input_failure :
    (q*qᴴ).PosSemidef ∧ ¬ (skewTransport ℝ q r (q*qᴴ)).PosSemidef := by
  rw [r_transpose]
  exact skewTransport_positive_input_obstruction q_square_zero arrow_nonzero

theorem signed_square_nonzero : skewTransport ℝ q r * skewTransport ℝ q r ≠ 0 := by
  intro h
  have he := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f p 0 0) h
  change skewTransport ℝ q r (skewTransport ℝ q r p) 0 0 = 0 at he
  norm_num [skewTransport_apply, p, q, r, mul_apply, Fin.sum_univ_succ] at he

/-- The two transport superoperators genuinely fail to commute. -/
theorem signed_symmetric_noncommute :
    crossTransport ℝ q r * skewTransport ℝ q r ≠
      skewTransport ℝ q r * crossTransport ℝ q r := by
  intro h
  have he := congrArg
    (fun f : Module.End ℝ (Matrix (Fin 4) (Fin 4) ℝ) => f p 0 0) h
  change crossTransport ℝ q r (skewTransport ℝ q r p) 0 0 =
    skewTransport ℝ q r (crossTransport ℝ q r p) 0 0 at he
  norm_num [skewTransport_apply, crossTransport_apply, p, q, r,
    mul_apply, Fin.sum_univ_succ] at he

/-- An independent dense probe detects failure of ambient centrality. -/
def probe : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,2,3,4; 2,1,5,3; 3,5,2,1; 4,3,1,2]

theorem quadratic_weight_not_central :
    (q*r+r*q)*probe ≠ probe*(q*r+r*q) := by
  intro h
  have he := congrArg (fun x : Matrix (Fin 4) (Fin 4) ℝ => x 0 1) h
  norm_num [q, r, probe, mul_apply, Fin.sum_univ_succ] at he

/-- The source's double commutator has a genuine nonscalar realization. -/
theorem double_commutator_realization :
    lieOp ℝ (q*r-r*q) (lieOp ℝ (q*r-r*q) (q+r)) =
      (4 : ℕ) • ((q*r+r*q)*(q*r+r*q)*(q+r)) := by
  have hr : r*r=0 := by
    rw [r_transpose, ← conjTranspose_mul, q_square_zero, conjTranspose_zero]
  exact pair_double_commutator_sum ℝ q_square_zero hr

end
end InfoGeometry.OperatorAlgebra.SignedTransportWitness
