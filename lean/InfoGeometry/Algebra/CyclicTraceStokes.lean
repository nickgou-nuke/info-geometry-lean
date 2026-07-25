import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace InfoGeometry.Algebra.CyclicTraceStokes

variable {n : Type*} [Fintype n]
variable {R : Type*} [CommRing R]

/-- Algebraic Cauchy Theorem: The trace of a commutator vanishes -/
theorem trace_commutator_zero_of_cyclic (A B : Matrix n n R) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- Cyclic trace forces boundary vanishing -/
theorem cyclic_trace_forces_boundary_zero (A B : Matrix n n R) :
    Matrix.trace (A * B) = Matrix.trace (B * A) →
    Matrix.trace (A * B - B * A) = 0 := by
  intro _
  exact trace_commutator_zero_of_cyclic A B

/-- Native Stokes' Theorem in the trace -/
theorem stokes_in_trace (A B : Matrix n n R) :
    Matrix.trace (A * B - B * A) = Matrix.trace (A * B) - Matrix.trace (B * A) := by
  rw [Matrix.trace_sub]

/-- Triple product cyclicity -/
theorem trace_mul_cycle_three (A B C : Matrix n n R) :
    Matrix.trace (A * B * C) = Matrix.trace (B * C * A) := by
  calc
    Matrix.trace (A * B * C) = Matrix.trace (A * (B * C)) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace ((B * C) * A) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (B * C * A) := by simp [Matrix.mul_assoc]

/-- Quadruple product cyclicity -/
theorem trace_mul_cycle_four (A B C D : Matrix n n R) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  calc
    Matrix.trace (A * B * C * D) = Matrix.trace (A * (B * C * D)) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace ((B * C * D) * A) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (B * C * D * A) := by simp [Matrix.mul_assoc]

end InfoGeometry.Algebra.CyclicTraceStokes
