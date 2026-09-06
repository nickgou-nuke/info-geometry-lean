import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# InfoGeometry.Prequantum.SouriauJaynesTrace

Finite algebraic trace bridge for the Jaynes--Souriau lane.

This file proves the closed finite matrix facts for this local trace bridge.
Broader Souriau, GNS, Tomita--Takesaki, and geometric-quantization lanes are
owned by their corresponding repository modules and are not re-proved here:

* the chosen `Cl(1,1)` coordinate atom has matrix trace `2 * tau`;
* conjugation by a supplied `SL(2, ℝ)` matrix unit is multiplicative;
* the trace pairing `Tr(XY)` is invariant under simultaneous conjugation.

The `SL2RUnit` type stores an actual matrix unit plus determinant-one evidence.
This avoids manufacturing inverses from determinant claims in this file.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace InfoGeometry.Prequantum.SouriauJaynesTrace

/-- Coordinate atom for the finite `Cl(1,1)` trace bridge. -/
structure Cl11TraceAtom where
  /-- Scalar coordinate. -/
  s : ℝ
  /-- First off-diagonal coordinate. -/
  e1 : ℝ
  /-- Split off-diagonal coordinate. -/
  e2 : ℝ
  /-- Diagonal pseudoscalar coordinate for this matrix chart. -/
  e12 : ℝ

/-- Scalar-coordinate trace functional. -/
def tau (X : Cl11TraceAtom) : ℝ :=
  X.s

/-- Standard `2 × 2` real matrix carrier. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- Matrix chart for the finite `Cl(1,1)` atom. -/
def toMatrix (q : Cl11TraceAtom) : Mat2 :=
  !![q.s + q.e12, q.e1 + q.e2;
     q.e1 - q.e2, q.s - q.e12]

/-- The matrix trace of this finite chart is twice the scalar trace `tau`. -/
theorem trace_toMatrix_eq_two_tau (q : Cl11TraceAtom) :
    Matrix.trace (toMatrix q) = 2 * tau q := by
  unfold toMatrix tau
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/--
Constructive `SL(2, ℝ)` matrix unit: an invertible `2 × 2` real matrix whose
determinant is one.
-/
structure SL2RUnit where
  /-- The underlying invertible matrix. -/
  unit : Mat2ˣ
  /-- Determinant-one condition. -/
  det_one : Matrix.det (unit : Mat2) = 1

/-- Adjoint/conjugation action by a supplied special-linear matrix unit. -/
def adjointAction (g : SL2RUnit) (X : Mat2) : Mat2 :=
  (g.unit : Mat2) * X * (↑g.unit⁻¹ : Mat2)

/-- Conjugation by a supplied matrix unit preserves multiplication. -/
theorem adjointAction_mul (g : SL2RUnit) (X Y : Mat2) :
    adjointAction g (X * Y) = adjointAction g X * adjointAction g Y := by
  unfold adjointAction
  calc
    (g.unit : Mat2) * (X * Y) * (↑g.unit⁻¹ : Mat2)
        = (g.unit : Mat2) * X * (Y * (↑g.unit⁻¹ : Mat2)) := by
            simp [Matrix.mul_assoc]
    _ = (g.unit : Mat2) * X * ((1 : Mat2) * (Y * (↑g.unit⁻¹ : Mat2))) := by
            rw [one_mul]
    _ = (g.unit : Mat2) * X *
          (((↑g.unit⁻¹ : Mat2) * (g.unit : Mat2)) * (Y * (↑g.unit⁻¹ : Mat2))) := by
            rw [Units.inv_mul]
    _ = (g.unit : Mat2) * X *
          ((↑g.unit⁻¹ : Mat2) * ((g.unit : Mat2) * (Y * (↑g.unit⁻¹ : Mat2)))) := by
            simp [Matrix.mul_assoc]
    _ = ((g.unit : Mat2) * X * (↑g.unit⁻¹ : Mat2)) *
          ((g.unit : Mat2) * Y * (↑g.unit⁻¹ : Mat2)) := by
            simp [Matrix.mul_assoc]

/-- Trace is invariant under conjugation by a supplied matrix unit. -/
theorem trace_adjointAction (g : SL2RUnit) (X : Mat2) :
    Matrix.trace (adjointAction g X) = Matrix.trace X := by
  unfold adjointAction
  exact Matrix.trace_units_conj g.unit X

/--
Finite Souriau/Jaynes trace-pairing equivariance under simultaneous conjugation.

This is a finite matrix identity for this trace bridge.  Broader coadjoint,
self-dual-cone, and completion statements live in their owner modules and are not
re-proved here.
-/
theorem souriau_momentum_equivariance (g : SL2RUnit) (X Y : Mat2) :
    Matrix.trace (adjointAction g X * adjointAction g Y) = Matrix.trace (X * Y) := by
  rw [← adjointAction_mul]
  exact trace_adjointAction g (X * Y)

end InfoGeometry.Prequantum.SouriauJaynesTrace
