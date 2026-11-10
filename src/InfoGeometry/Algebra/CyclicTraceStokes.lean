/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix

namespace InfoGeometry.Algebra.CyclicTraceStokes

section NonCommutativeRingTrace

variable {B M : Type*} [Ring B] [AddCommGroup M]

/-- Over any non-commutative ring `B` equipped with a cyclic additive functional `τ : B →+ M`,
the trace of a commutator vanishes: `τ (A * C - C * A) = 0`. -/
theorem trace_commutator_zero_of_cyclic_ring
    (τ : B →+ M) (hcyc : ∀ x y : B, τ (x * y) = τ (y * x)) (A C : B) :
    τ (A * C - C * A) = 0 := by
  rw [map_sub, hcyc A C, sub_self]

/-- Over any non-commutative ring `B` equipped with a cyclic additive functional `τ : B →+ M`,
triple products are invariant under cyclic permutation: `τ (A * C * D) = τ (C * D * A)`. -/
theorem trace_mul_cycle_three_ring
    (τ : B →+ M) (hcyc : ∀ x y : B, τ (x * y) = τ (y * x)) (A C D : B) :
    τ (A * C * D) = τ (C * D * A) := by
  calc
    τ (A * C * D) = τ (A * (C * D)) := by rw [mul_assoc]
    _ = τ ((C * D) * A) := hcyc A (C * D)
    _ = τ (C * D * A) := rfl

/-- Over any non-commutative ring `B` equipped with a cyclic additive functional `τ : B →+ M`,
quadruple products are invariant under cyclic permutation: `τ (A * C * D * E) = τ (C * D * E * A)`. -/
theorem trace_mul_cycle_four_ring
    (τ : B →+ M) (hcyc : ∀ x y : B, τ (x * y) = τ (y * x)) (A C D E : B) :
    τ (A * C * D * E) = τ (C * D * E * A) := by
  calc
    τ (A * C * D * E) = τ (A * (C * D * E)) := by simp only [mul_assoc]
    _ = τ ((C * D * E) * A) := hcyc A (C * D * E)
    _ = τ (C * D * E * A) := rfl

end NonCommutativeRingTrace

variable {n : Type*} [Fintype n]

/-- Algebraic Cauchy Theorem: The trace of a commutator vanishes -/
theorem trace_commutator_zero_of_cyclic {R : Type*} [CommRing R] (A B : Matrix n n R) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- Cyclic trace forces boundary vanishing over any ring `[Ring R]`. -/
theorem cyclic_trace_forces_boundary_zero {R : Type*} [Ring R] (A B : Matrix n n R) :
    Matrix.trace (A * B) = Matrix.trace (B * A) →
    Matrix.trace (A * B - B * A) = 0 := by
  intro h
  rw [Matrix.trace_sub, h, sub_self]

/-- Native Stokes' Theorem in the trace over any ring `[Ring R]`. -/
theorem stokes_in_trace {R : Type*} [Ring R] (A B : Matrix n n R) :
    Matrix.trace (A * B - B * A) = Matrix.trace (A * B) - Matrix.trace (B * A) := by
  rw [Matrix.trace_sub]

/-- Triple product cyclicity -/
theorem trace_mul_cycle_three {R : Type*} [CommRing R] (A B C : Matrix n n R) :
    Matrix.trace (A * B * C) = Matrix.trace (B * C * A) := by
  calc
    Matrix.trace (A * B * C) = Matrix.trace (A * (B * C)) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace ((B * C) * A) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (B * C * A) := by simp [Matrix.mul_assoc]

/-- Quadruple product cyclicity -/
theorem trace_mul_cycle_four {R : Type*} [CommRing R] (A B C D : Matrix n n R) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  calc
    Matrix.trace (A * B * C * D) = Matrix.trace (A * (B * C * D)) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace ((B * C * D) * A) := by rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (B * C * D * A) := by simp [Matrix.mul_assoc]

open InfoGeometry.Algebra.FiniteSpin in
/-- Non-commutativity witness for the finite spin operator carrier. -/
theorem cyclic_stokes_spin_carrier_noncomm : J_plus * J_minus ≠ J_minus * J_plus :=
  j_plus_j_minus_ne

end InfoGeometry.Algebra.CyclicTraceStokes
