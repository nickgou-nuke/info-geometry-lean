/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ChiralProjectorBerryCurvature
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Rectangular stabilization of projector curvature

The carriers are native finite rectangular matrices over a commutative ring.
For a split embedding `V * U = 1`, the ordered lift is `A ↦ U * A * V`.
Adding a fixed idempotent `E` with `E * U = 0` and `V * E = 0` preserves
idempotence, the algebraic tangent equation, and the existing compressed
projector-curvature coefficient. Rectangular trace cyclicity preserves its
trace and the one-sided curvature trace used in projector comparisons.

This is the finite algebra behind the fixed-complement comparison in
Nathaniel Craig, *A gauge-invariant measure for lattice chiral fermions*,
arXiv:2610.09093v1, equation (72). The external formalization includes an
isometric complex-matrix version (`isometricEmbedding_curvature_trace`).
Here the retraction `V` is explicit and no scalar or matrix commutativity is
assumed beyond commutativity of the coefficient ring. The lift need not
preserve the ambient unit: it sends `1` to `U * V`.

No differentiability, spectral gap, determinant transport, convergence,
global fermion measure, or continuum statement is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.RectangularProjectorStabilization

open InfoGeometry.Clifford.ChiralProjectorBerryCurvature

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

variable (U : Matrix m n R) (V : Matrix n m R)

/-- The ordered rectangular lift through an embedding and a retraction. -/
def liftMatrix (A : Matrix n n R) : Matrix m m R := U * A * V

/-- A fixed complementary sector added to the rectangular lift. -/
def stabilize (P : Matrix n n R) (E : Matrix m m R) : Matrix m m R :=
  liftMatrix U V P + E

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem liftMatrix_add (A B : Matrix n n R) :
    liftMatrix U V (A + B) = liftMatrix U V A + liftMatrix U V B := by
  simp only [liftMatrix, Matrix.mul_add, Matrix.add_mul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem liftMatrix_sub (A B : Matrix n n R) :
    liftMatrix U V (A - B) = liftMatrix U V A - liftMatrix U V B := by
  simp only [liftMatrix, Matrix.mul_sub, Matrix.sub_mul]

omit [Fintype m] [DecidableEq m] in
/-- The ambient unit is the range idempotent, not necessarily the full unit. -/
theorem liftMatrix_one : liftMatrix U V 1 = U * V := by
  simp only [liftMatrix, Matrix.mul_one]

omit [DecidableEq m] in
/-- A split embedding preserves products in their original order. -/
theorem liftMatrix_mul (hVU : V * U = 1) (A B : Matrix n n R) :
    liftMatrix U V A * liftMatrix U V B = liftMatrix U V (A * B) := by
  simp only [liftMatrix, Matrix.mul_assoc, ← Matrix.mul_assoc V U,
    hVU, Matrix.one_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- The fixed sector annihilates every lifted matrix on the left. -/
theorem complement_mul_lift {E : Matrix m m R} (hEU : E * U = 0)
    (A : Matrix n n R) : E * liftMatrix U V A = 0 := by
  unfold liftMatrix
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEU,
    Matrix.zero_mul, Matrix.zero_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- The fixed sector annihilates every lifted matrix on the right. -/
theorem lift_mul_complement {E : Matrix m m R} (hVE : V * E = 0)
    (A : Matrix n n R) : liftMatrix U V A * E = 0 := by
  unfold liftMatrix
  rw [Matrix.mul_assoc, hVE, Matrix.mul_zero]

omit [DecidableEq m] in
theorem stabilize_mul_lift (hVU : V * U = 1) {E : Matrix m m R}
    (hEU : E * U = 0) (P A : Matrix n n R) :
    stabilize U V P E * liftMatrix U V A = liftMatrix U V (P * A) := by
  rw [stabilize, Matrix.add_mul, liftMatrix_mul U V hVU,
    complement_mul_lift U V hEU, add_zero]

omit [DecidableEq m] in
theorem lift_mul_stabilize (hVU : V * U = 1) {E : Matrix m m R}
    (hVE : V * E = 0) (A P : Matrix n n R) :
    liftMatrix U V A * stabilize U V P E = liftMatrix U V (A * P) := by
  rw [stabilize, Matrix.mul_add, liftMatrix_mul U V hVU,
    lift_mul_complement U V hVE, add_zero]

omit [DecidableEq m] in
/-- An idempotent on the embedded space and a disjoint fixed idempotent
give an idempotent on the full space. -/
theorem stabilize_idempotent (hVU : V * U = 1) {P : Matrix n n R}
    {E : Matrix m m R} (hP : P * P = P) (hE : E * E = E)
    (hEU : E * U = 0) (hVE : V * E = 0) :
    stabilize U V P E * stabilize U V P E = stabilize U V P E := by
  unfold stabilize
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    liftMatrix_mul U V hVU, lift_mul_complement U V hVE,
    complement_mul_lift U V hEU, hP, hE]
  simp only [add_zero, zero_add]

omit [DecidableEq m] in
/-- The first-order idempotent equation survives a fixed complementary sector. -/
theorem stabilize_tangent (hVU : V * U = 1) {E : Matrix m m R}
    (hEU : E * U = 0) (hVE : V * E = 0) {P A : Matrix n n R}
    (hA : P * A + A * P = A) :
    stabilize U V P E * liftMatrix U V A +
      liftMatrix U V A * stabilize U V P E = liftMatrix U V A := by
  rw [stabilize_mul_lift U V hVU hEU, lift_mul_stabilize U V hVU hVE,
    ← liftMatrix_add U V, hA]

/-- The lift preserves the genuine noncommutative bracket. -/
theorem commutator_lift (hVU : V * U = 1) (A B : Matrix n n R) :
    commutator (liftMatrix U V A) (liftMatrix U V B) =
      liftMatrix U V (commutator A B) := by
  unfold commutator
  rw [liftMatrix_mul U V hVU, liftMatrix_mul U V hVU, ← liftMatrix_sub U V]

/-- The fixed sector contributes no compressed projector curvature. -/
theorem projectorCurvature_stabilize (hVU : V * U = 1)
    {E : Matrix m m R} (hEU : E * U = 0) (hVE : V * E = 0)
    (P A B : Matrix n n R) :
    projectorCurvature (stabilize U V P E) (liftMatrix U V A) (liftMatrix U V B) =
      liftMatrix U V (projectorCurvature P A B) := by
  unfold projectorCurvature
  rw [commutator_lift U V hVU, stabilize_mul_lift U V hVU hEU,
    lift_mul_stabilize U V hVU hVE]

omit [DecidableEq m] in
/-- Cyclicity for rectangular products gives exact trace preservation. -/
theorem trace_liftMatrix (hVU : V * U = 1) (A : Matrix n n R) :
    Matrix.trace (liftMatrix U V A) = Matrix.trace A := by
  unfold liftMatrix
  rw [Matrix.trace_mul_cycle, hVU, Matrix.one_mul]

/-- The one-sided curvature trace from the finite comparison identity
is unchanged by a split embedding and a fixed disjoint sector. -/
theorem trace_stabilize_commutator (hVU : V * U = 1)
    {E : Matrix m m R} (hEU : E * U = 0) (P A B : Matrix n n R) :
    Matrix.trace
        (stabilize U V P E * commutator (liftMatrix U V A) (liftMatrix U V B)) =
      Matrix.trace (P * commutator A B) := by
  rw [commutator_lift U V hVU, stabilize_mul_lift U V hVU hEU,
    trace_liftMatrix U V hVU]

/-- The trace of the existing compressed curvature owner is also preserved. -/
theorem trace_projectorCurvature_stabilize (hVU : V * U = 1)
    {E : Matrix m m R} (hEU : E * U = 0) (hVE : V * E = 0)
    (P A B : Matrix n n R) :
    Matrix.trace
        (projectorCurvature (stabilize U V P E) (liftMatrix U V A) (liftMatrix U V B)) =
      Matrix.trace (projectorCurvature P A B) := by
  rw [projectorCurvature_stabilize U V hVU hEU hVE, trace_liftMatrix U V hVU]

end InfoGeometry.OperatorAlgebra.RectangularProjectorStabilization
