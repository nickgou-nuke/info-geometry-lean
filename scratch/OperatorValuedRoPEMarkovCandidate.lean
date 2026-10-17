/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Routing.DiscreteRoPERepresentation
import InfoGeometry.Routing.PlanarRotation
import InfoGeometry.QuantumContext.FiniteMarkovTransitionKernel

/-!
# Operator-valued Markov pooling with position-dependent RoPE

This scratch candidate combines the existing finite row-stochastic transition
carrier with the repository's planar RoPE rotor.  The operator fiber is the
full, noncommutative algebra `Matrix (Fin 2) (Fin 2) ℝ`.

The central result is an exact defect formula for the failure of positionwise
RoPE conjugation to commute with Markov pooling. A concrete two-token witness
shows this defect is nonzero on noncommuting matrix units. The fixed-rotor
linearity identity is retained as a corollary.

This file makes no claim about gravitational forces, spirals, density waves,
or limiting dynamics.
-/

open scoped BigOperators

namespace InfoGeometry.Scratch.OperatorValuedRoPEMarkov

abbrev Token := Fin 2
abbrev Operator := Matrix (Fin 2) (Fin 2) ℝ

open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.Routing.PlanarRotation

/-- A row-wise weighted average of operator-valued token data. -/
def operatorPool (P : Matrix Token Token ℝ) (X : Token → Operator) :
    Token → Operator :=
  fun i => ∑ j, P i j • X j

/-- Conjugation by one fixed real matrix, acting linearly on the full matrix
algebra. -/
def conjugateLinear (R : Operator) : Operator →ₗ[ℝ] Operator where
  toFun X := R * X * Rᵀ
  map_add' X Y := by
    simp only [add_mul, mul_add]
  map_smul' c X := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    ring

/-- The uniform position-`m` RoPE action on an operator fiber. -/
def ropeConjugate (θ : ℝ) (m : ℤ) (X : Operator) : Operator :=
  conjugateLinear (ropeRotor θ m) X

/-- RoPE position attached to each of the two token indices. -/
def tokenPosition : Token → ℤ := fun i => if i = 0 then 0 else 1

/-- Conjugate each operator by the rotor at its own token position. -/
def positionwiseConjugate (θ : ℝ) (position : Token → ℤ)
    (X : Token → Operator) : Token → Operator :=
  fun i => ropeConjugate θ (position i) (X i)

/-- The position-dependent Markov/RoPE defect is the pooled conjugated family
minus conjugation at the output position of the pooled family. -/
def positionwiseDefect (P : Matrix Token Token ℝ) (X : Token → Operator)
    (θ : ℝ) (position : Token → ℤ) : Token → Operator :=
  fun i => operatorPool P (positionwiseConjugate θ position X) i -
    ropeConjugate θ (position i) (operatorPool P X i)

/-- Exact positionwise obstruction formula. The carrier is a token-indexed
family of full `2 × 2` real matrices; the sums are over the finite token
index, and no stochasticity assumption is required for this identity. -/
theorem positionwiseDefect_eq_sum (P : Matrix Token Token ℝ)
    (X : Token → Operator) (θ : ℝ) (position : Token → ℤ) (i : Token) :
    positionwiseDefect P X θ position i =
      ∑ j, P i j • (ropeConjugate θ (position j) (X j) -
        ropeConjugate θ (position i) (X j)) := by
  classical
  unfold positionwiseDefect positionwiseConjugate operatorPool
  rw [map_sum, map_smul, ← Finset.sum_sub_distrib]
  simp only [smul_sub]

/-- In the uniform-position case, the defect vanishes: one fixed linear
conjugation commutes with operator-valued pooling. -/
theorem ropeConjugate_operatorPool (P : Matrix Token Token ℝ)
    (X : Token → Operator) (θ : ℝ) (m : ℤ) (i : Token) :
    operatorPool P (fun j => ropeConjugate θ m (X j)) i =
      ropeConjugate θ m (operatorPool P X i) := by
  classical
  unfold operatorPool ropeConjugate
  simpa only [map_smul] using
    (map_sum (conjugateLinear (ropeRotor θ m)) Finset.univ
      (fun j => P i j • X j)).symm

/-- For a row-stochastic transition, operator pooling preserves the constant
identity-valued family (unitality of this linear pooling action). -/
theorem operatorPool_const_one (P : Matrix Token Token ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Token) (i : Token) :
    operatorPool P (fun _ : Token => (1 : Operator)) i = 1 := by
  classical
  unfold operatorPool
  rw [← Finset.sum_smul]
  rw [Matrix.sum_row_of_mem_rowStochastic hP i]
  simp

def transition : Matrix Token Token ℝ := !![(3 / 4 : ℝ), 1 / 4; 1 / 4, 3 / 4]

theorem transition_rowStochastic :
    transition ∈ Matrix.rowStochastic ℝ Token := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [transition]
  · intro i
    fin_cases i <;> norm_num [transition]

def e01 : Operator := !![(0 : ℝ), 1; 0, 0]
def e10 : Operator := !![(0 : ℝ), 0; 1, 0]

/-- A two-position family using the two off-diagonal matrix units. -/
def Z : Token → Operator := fun i => if i = 0 then e10 else e01

theorem Z_fibers_noncommute : Z 0 * Z 1 ≠ Z 1 * Z 0 := by
  norm_num [Z, e01, e10, Matrix.mul_apply]

/-- The zero-position rotor is the identity. -/
theorem tokenPosition_rotor_zero :
    ropeRotor (Real.pi / 2) (tokenPosition 0) = (1 : Operator) := by
  norm_num [tokenPosition, ropeRotor, rotation]

/-- At position one and angle `π/2`, the existing RoPE rotor is the quarter
turn represented by the standard real rotation matrix. -/
theorem tokenPosition_rotor_one :
    ropeRotor (Real.pi / 2) (tokenPosition 1) = !![(0 : ℝ), -1; 1, 0] := by
  norm_num [tokenPosition, ropeRotor, rotation, Real.cos_pi_div_two,
    Real.sin_pi_div_two]

/-- This quarter-turn conjugates the upper matrix unit to minus the lower
matrix unit. -/
theorem quarterTurn_conjugates_e01 :
    ropeConjugate (Real.pi / 2) 1 e01 = -e10 := by
  unfold ropeConjugate conjugateLinear
  rw [show ropeRotor (Real.pi / 2) 1 = !![(0 : ℝ), -1; 1, 0] by
    norm_num [ropeRotor, rotation, Real.cos_pi_div_two, Real.sin_pi_div_two]]
  norm_num [e01, e10, Matrix.mul_apply, Matrix.transpose_apply]

/-- Two genuinely noncommuting matrix-valued token observables. -/
def X : Token → Operator := fun i => if i = 0 then e01 else 0
def Y : Token → Operator := fun i => if i = 0 then e10 else 0

/-- The witness fiber is the full noncommutative matrix algebra: its two
matrix units have distinct products in opposite orders. -/
theorem witness_noncommuting : X 0 * Y 0 ≠ Y 0 * X 0 := by
  norm_num [X, Y, e01, e10, Matrix.mul_apply]

/-- For a non-diagonal stochastic transition, pooling these operator-valued
families does not preserve their pointwise product. -/
theorem transition_pool_not_multiplicative :
    operatorPool transition (fun i => X i * Y i) 0 ≠
      operatorPool transition X 0 * operatorPool transition Y 0 := by
  intro h
  have hentry := congrArg (fun A : Operator => A 0 0) h
  norm_num [operatorPool, transition, X, Y, e01, e10, Matrix.mul_apply] at hentry

/-- For the non-diagonal row-stochastic transition, positions `0` and `1`,
and the noncommuting matrix-unit family `Z`, the position-dependent defect is
nonzero. The `(0,1)` matrix entry is already a nonzero rational number. -/
theorem positionwiseDefect_nonzero_witness :
    positionwiseDefect transition Z (Real.pi / 2) tokenPosition 0 ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Operator => A 0 1) h
  norm_num [positionwiseDefect, positionwiseConjugate, operatorPool,
    transition, tokenPosition, Z, e01, e10, ropeConjugate, conjugateLinear,
    ropeRotor, rotation, Matrix.mul_apply, Matrix.transpose_apply,
    Real.cos_pi_div_two, Real.sin_pi_div_two] at hentry

end InfoGeometry.Scratch.OperatorValuedRoPEMarkov
