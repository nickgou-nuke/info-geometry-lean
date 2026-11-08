/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Routing.DiscreteRoPERepresentation
import InfoGeometry.Routing.PlanarRotation

/-!
# Finite operator-valued Markov/RoPE pooling defect

The token carrier and operator fiber are both concrete `Fin 2` carriers. The
main identity records the exact defect for position-dependent rotor
conjugation and finite Markov pooling. The witness uses the full noncommutative
real `2 × 2` matrix algebra.
-/

open scoped BigOperators

namespace InfoGeometry.Routing.OperatorValuedRoPEMarkov

abbrev Token := Fin 2
abbrev Op := Matrix (Fin 2) (Fin 2) ℝ

open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.Routing.PlanarRotation

noncomputable section

/-- Finite row-wise pooling of operator-valued token data. -/
def pool (P : Matrix Token Token ℝ) (X : Token → Op) : Token → Op :=
  fun i => ∑ j, P i j • X j

/-- Conjugation by the existing integer-position RoPE rotor. -/
def conjugate (θ : ℝ) (m : ℤ) (A : Op) : Op :=
  ropeRotor θ m * A * Matrix.transpose (ropeRotor θ m)

/-- Position-dependent conjugation of each operator in the token family. -/
def positionwise (θ : ℝ) (position : Token → ℤ) (X : Token → Op) :
    Token → Op :=
  fun i => conjugate θ (position i) (X i)

/-- Difference between pooling after positionwise conjugation and conjugating
the pooled operator at the output token position. -/
def defect (P : Matrix Token Token ℝ) (X : Token → Op) (θ : ℝ)
    (position : Token → ℤ) : Token → Op :=
  fun i => pool P (positionwise θ position X) i -
    conjugate θ (position i) (pool P X i)

/-- Exact finite defect identity. -/
theorem defect_eq_sum (P : Matrix Token Token ℝ) (X : Token → Op)
    (θ : ℝ) (position : Token → ℤ) (i : Token) :
    defect P X θ position i =
      ∑ j, P i j • (conjugate θ (position j) (X j) -
        conjugate θ (position i) (X j)) := by
  classical
  ext a b
  simp [defect, pool, positionwise, conjugate, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

def transition : Matrix Token Token ℝ := !![(3 / 4 : ℝ), 1 / 4; 1 / 4, 3 / 4]

/-- The concrete non-diagonal transition used in the witness is row-stochastic. -/
theorem transition_rowStochastic :
    transition ∈ Matrix.rowStochastic ℝ Token := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [transition]
  · intro i
    fin_cases i <;> norm_num [transition]

def e01 : Op := !![(0 : ℝ), 1; 0, 0]
def e10 : Op := !![(0 : ℝ), 0; 1, 0]

def positions : Token → ℤ := fun i => if i = 0 then 0 else 1

def witnessFamily : Token → Op := fun i => if i = 0 then e10 else e01

/-- The two matrix units in the witness genuinely fail to commute. -/
theorem matrixUnits_noncommute : e01 * e10 ≠ e10 * e01 := by
  norm_num [e01, e10, Matrix.mul_apply]

/-- The chosen quarter-turn position acts by the existing rotor as expected. -/
theorem rotor_at_position_one :
    ropeRotor (Real.pi / 2) (positions 1) = !![(0 : ℝ), -1; 1, 0] := by
  norm_num [positions, ropeRotor, InfoGeometry.Routing.PlanarRotation.rotation,
    Real.cos_pi_div_two,
    Real.sin_pi_div_two]

/-- Concrete nonzero defect for the non-diagonal two-state stochastic
transition, positions zero and one, and noncommuting matrix-unit data. -/
theorem nonzero_defect_witness :
    defect transition witnessFamily (Real.pi / 2) positions 0 ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Op => A 0 1) h
  norm_num [defect, pool, positionwise, conjugate, transition, positions,
    witnessFamily, e01, e10, ropeRotor,
    InfoGeometry.Routing.PlanarRotation.rotation, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Real.cos_pi_div_two,
    Real.sin_pi_div_two] at hentry

end

end InfoGeometry.Routing.OperatorValuedRoPEMarkov
