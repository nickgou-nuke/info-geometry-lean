/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite algebraic core for Arnold's volume-preserving group

This owner gives a finite-dimensional algebraic analogue of the group and Lie
algebra appearing in Arnold's geometric approach to ideal hydrodynamics and
Navier--Stokes:

- the determinant-one linear group `SL(n, ℝ)` as the finite volume-preserving
  group;
- traceless matrices as the finite divergence-free / incompressible Lie
  algebra;
- closure of that Lie algebra under the matrix commutator.

This is not the infinite-dimensional group `SDiff(M)` of volume-preserving
diffeomorphisms and does not prove the Navier--Stokes Euler--Arnold equation.
Those remain explicit open debts.
-/

noncomputable section

namespace InfoGeometry.Physics.ArnoldFiniteGroupCore

/-- Finite volume-preserving linear group: the determinant-one matrices. -/
abbrev ArnoldFiniteGroup (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ

/-- Determinant-one law for the finite Arnold group. -/
theorem arnoldFiniteGroup_det_one (n : ℕ) (g : ArnoldFiniteGroup n) :
    Matrix.det (g : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  exact Matrix.SpecialLinearGroup.det_coe g

/-- Finite divergence-free / incompressible generator condition. -/
def IsTraceless (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.trace X = 0

/-- The finite incompressible cone is closed under addition. -/
theorem isTraceless_add (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℝ)
    (hX : IsTraceless n X) (hY : IsTraceless n Y) :
    IsTraceless n (X + Y) := by
  dsimp [IsTraceless] at hX hY ⊢
  rw [Matrix.trace_add, hX, hY, zero_add]

/-- The finite incompressible cone is closed under real scaling. -/
theorem isTraceless_smul (n : ℕ) (c : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : IsTraceless n X) :
    IsTraceless n (c • X) := by
  dsimp [IsTraceless] at hX ⊢
  rw [Matrix.trace_smul, hX]
  simp

/-- Lie-bracket closure of the finite incompressible Lie algebra. -/
theorem arnoldFinite_traceless_commutator (n : ℕ)
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    IsTraceless n (X * Y - Y * X) := by
  dsimp [IsTraceless]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

end InfoGeometry.Physics.ArnoldFiniteGroupCore
