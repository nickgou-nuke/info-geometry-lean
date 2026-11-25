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

/-- Adjoint preservation of finite incompressibility: conjugation by a
determinant-one volume-preserving matrix keeps a traceless generator traceless. -/
theorem arnoldFiniteGroup_adjoint_traceless (n : ℕ) (g : ArnoldFiniteGroup n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsTraceless n X) :
    IsTraceless n ((g : Matrix (Fin n) (Fin n) ℝ) * X *
      ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ)) := by
  have hginv : ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ) *
      (g : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  dsimp [IsTraceless] at hX ⊢
  calc
    Matrix.trace ((g : Matrix (Fin n) (Fin n) ℝ) * X *
        ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ))
        = Matrix.trace (((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ) *
            ((g : Matrix (Fin n) (Fin n) ℝ) * X)) := by
              rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ) *
          (g : Matrix (Fin n) (Fin n) ℝ)) * X) := by rw [mul_assoc]
    _ = Matrix.trace (1 * X) := by rw [hginv]
    _ = Matrix.trace X := by simp
    _ = 0 := hX

/-- The finite incompressible generators form a real submodule of matrix space. -/
def arnoldFiniteLieModule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | IsTraceless n X}
  zero_mem' := by
    dsimp [IsTraceless]
    simp
  add_mem' := by
    intro X Y hX hY
    change IsTraceless n X at hX
    change IsTraceless n Y at hY
    change IsTraceless n (X + Y)
    exact isTraceless_add n X Y hX hY
  smul_mem' := by
    intro c X hX
    change IsTraceless n X at hX
    change IsTraceless n (c • X)
    exact isTraceless_smul n c X hX

/-- The commutator of any two matrices lies in the finite incompressible module. -/
theorem arnoldFiniteLieModule_bracket_mem (n : ℕ)
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    X * Y - Y * X ∈ arnoldFiniteLieModule n := by
  change IsTraceless n (X * Y - Y * X)
  exact arnoldFinite_traceless_commutator n X Y

/-- The finite Arnold group acts on the incompressible module by conjugation. -/
theorem arnoldFiniteGroup_adjoint_mem (n : ℕ) (g : ArnoldFiniteGroup n)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X ∈ arnoldFiniteLieModule n) :
    (g : Matrix (Fin n) (Fin n) ℝ) * X *
      ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ) ∈
        arnoldFiniteLieModule n := by
  change IsTraceless n X at hX
  change IsTraceless n ((g : Matrix (Fin n) (Fin n) ℝ) * X *
    ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ))
  exact arnoldFiniteGroup_adjoint_traceless n g X hX

/-- Trace pairing is invariant under the finite Arnold adjoint action;
this is the finite analogue of conservation of the helicity/Casimir pairing. -/
theorem arnoldFiniteGroup_tracePairing_invariant (n : ℕ) (g : ArnoldFiniteGroup n)
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (((g : Matrix (Fin n) (Fin n) ℝ) * X *
        ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ)) *
      ((g : Matrix (Fin n) (Fin n) ℝ) * Y *
        ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ))) =
    Matrix.trace (X * Y) := by
  let gg : Matrix (Fin n) (Fin n) ℝ := g
  let gh : Matrix (Fin n) (Fin n) ℝ := (g⁻¹ : ArnoldFiniteGroup n)
  have hhg0 : ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ) *
      (g : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hhg : gh * gg = 1 := by simpa [gh, gg] using hhg0
  change Matrix.trace ((gg * X * gh) * (gg * Y * gh)) = Matrix.trace (X * Y)
  calc
    Matrix.trace ((gg * X * gh) * (gg * Y * gh))
        = Matrix.trace ((gg * X) * (gh * gg) * Y * gh) := by
            congr 1
            ac_rfl
    _ = Matrix.trace ((gg * X) * 1 * Y * gh) := by rw [hhg]
    _ = Matrix.trace ((gg * (X * Y)) * gh) := by
            congr 1
            simp only [mul_assoc, one_mul]
    _ = Matrix.trace (gh * gg * (X * Y)) := by
            rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (1 * (X * Y)) := by rw [hhg]
    _ = Matrix.trace (X * Y) := by simp

/-- Quadratic trace invariant of a finite incompressible generator. -/
theorem arnoldFiniteGroup_quadratic_trace_invariant (n : ℕ)
    (g : ArnoldFiniteGroup n) (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (((g : Matrix (Fin n) (Fin n) ℝ) * X *
        ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ)) *
      ((g : Matrix (Fin n) (Fin n) ℝ) * X *
        ((g⁻¹ : ArnoldFiniteGroup n) : Matrix (Fin n) (Fin n) ℝ))) =
    Matrix.trace (X * X) :=
  arnoldFiniteGroup_tracePairing_invariant n g X X

/-- Infinitesimal adjoint invariance of the trace pairing:
`⟪[Z,X],Y⟫ + ⟪X,[Z,Y]⟫ = 0`.
This is the finite algebraic form of Euler--Arnold/Casimir conservation. -/
theorem arnoldFiniteGroup_ad_invariant_tracePairing {n : ℕ}
    (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace ((Z * X - X * Z) * Y) + Matrix.trace (X * (Z * Y - Y * Z)) = 0 := by
  rw [sub_mul, Matrix.trace_sub, mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_cycle Z X Y]
  rw [Matrix.trace_mul_cycle Y Z X]
  simp only [mul_assoc]
  ring

end InfoGeometry.Physics.ArnoldFiniteGroupCore
