/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Coordinates and contact generators for the real symplectic Lie algebra in dimension four

The carrier is Mathlib's native Lie subalgebra of matrices skew-adjoint for
`omega`. An explicit linear equivalence with ten real coordinates proves its
dimension. The coordinates are ordered by contact degree: one coordinate in
degree -2, two in degree -1, four in degree 0, two in degree 1 and one in
degree 2. The grading itself is constructed in `Sp4ContactGrading`.

All products below are full ordered matrix products. The endpoint matrices
`zPlus` and `zMinus` are normalized matrix units; the brackets of the degree-one
generators are respectively `-2 • zPlus` and `2 • zMinus`.
-/

noncomputable section

namespace InfoGeometry.Algebra.Sp4Contact

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

/-- Symplectic form adapted to the split of dimensions `1 + 2 + 1`. -/
def omega : Mat :=
  !![0, 0, 0, 1;
     0, 0, -1, 0;
     0, 1, 0, 0;
     -1, 0, 0, 0]

/-- Native symplectic matrix Lie subalgebra in the chosen basis. -/
abbrev algebra : LieSubalgebra ℝ Mat := skewAdjointMatricesLieSubalgebra omega

/-- The full ten-dimensional real symplectic Lie algebra for `omega`. -/
abbrev Sp : Type := algebra

theorem omega_transpose : omega.transpose = -omega := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [omega]

theorem omega_sq : omega * omega = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omega, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mem_algebra_iff (X : Mat) :
    X ∈ algebra ↔ X.transpose * omega + omega * X = 0 := by
  simp only [algebra, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
    Matrix.mul_neg, ← eq_neg_iff_add_eq_zero]

theorem symplectic_equation (X : Sp) :
    (X : Mat).transpose * omega = omega * -(X : Mat) := by
  simpa only [algebra, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
    using X.property

/-- General matrix satisfying the symplectic equation, in ten independent coordinates. -/
def matrixOfCoordinates (c : Fin 10 → ℝ) : Mat :=
  !![c 3, c 7, c 8, c 9;
     c 1, c 4, c 5, -c 8;
     c 2, c 6, -c 4, c 7;
     c 0, -c 2, c 1, -c 3]

theorem matrixOfCoordinates_mem (c : Fin 10 → ℝ) :
    matrixOfCoordinates c ∈ algebra := by
  rw [mem_algebra_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfCoordinates, omega, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Read the ten free entries from a symplectic matrix. -/
def coordinates (X : Sp) : Fin 10 → ℝ :=
  ![(X : Mat) 3 0, (X : Mat) 1 0, (X : Mat) 2 0, (X : Mat) 0 0,
    (X : Mat) 1 1, (X : Mat) 1 2, (X : Mat) 2 1,
    (X : Mat) 0 1, (X : Mat) 0 2, (X : Mat) 0 3]

theorem matrixOfCoordinates_coordinates (X : Sp) :
    matrixOfCoordinates (coordinates X) = (X : Mat) := by
  have h := symplectic_equation X
  have h01 := congrArg (fun M : Mat => M 0 1) h
  have h02 := congrArg (fun M : Mat => M 0 2) h
  have h03 := congrArg (fun M : Mat => M 0 3) h
  have h12 := congrArg (fun M : Mat => M 1 2) h
  have h13 := congrArg (fun M : Mat => M 1 3) h
  have h23 := congrArg (fun M : Mat => M 2 3) h
  simp [omega, Matrix.mul_apply, Fin.sum_univ_succ] at h01 h02 h03 h12 h13 h23
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfCoordinates, coordinates] <;> linarith

/-- Explicit coordinates give a linear equivalence with the actual native Lie algebra. -/
def coordinateEquiv : (Fin 10 → ℝ) ≃ₗ[ℝ] Sp where
  toFun c := ⟨matrixOfCoordinates c, matrixOfCoordinates_mem c⟩
  invFun := coordinates
  left_inv c := by
    funext i
    fin_cases i <;> simp [coordinates, matrixOfCoordinates]
  right_inv X := Subtype.ext (matrixOfCoordinates_coordinates X)
  map_add' c d := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixOfCoordinates] <;> ring
  map_smul' r c := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixOfCoordinates]

@[simp] theorem coe_coordinateEquiv (c : Fin 10 → ℝ) :
    (coordinateEquiv c : Mat) = matrixOfCoordinates c := rfl

@[simp] theorem coordinateEquiv_symm_apply (X : Sp) :
    coordinateEquiv.symm X = coordinates X := rfl

@[simp] theorem coordinates_coordinateEquiv (c : Fin 10 → ℝ) :
    coordinates (coordinateEquiv c) = c := coordinateEquiv.left_inv c

theorem coordinates_injective : Function.Injective coordinates :=
  coordinateEquiv.symm.injective

@[simp] theorem coordinates_zero : coordinates (0 : Sp) = 0 :=
  coordinateEquiv.symm.map_zero

@[simp] theorem coordinates_add (X Y : Sp) :
    coordinates (X + Y) = coordinates X + coordinates Y :=
  coordinateEquiv.symm.map_add X Y

@[simp] theorem coordinates_smul (r : ℝ) (X : Sp) :
    coordinates (r • X) = r • coordinates X :=
  coordinateEquiv.symm.map_smul r X

theorem finrank_sp : Module.finrank ℝ Sp = 10 := by
  rw [← coordinateEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

/-- Coordinate basis vector viewed as a symplectic matrix. -/
def generator (i : Fin 10) : Sp := coordinateEquiv (Pi.single i 1)

def zMinus : Sp := generator 0
def v1 : Sp := generator 1
def v2 : Sp := generator 2
def gradingElement : Sp := generator 3
def middleDiagonal : Sp := generator 4
def middleUpper : Sp := generator 5
def middleLower : Sp := generator 6
def u1 : Sp := generator 7
def u2 : Sp := generator 8
def zPlus : Sp := generator 9

theorem gradingElement_matrix :
    (gradingElement : Mat) = !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gradingElement, generator, matrixOfCoordinates, Pi.single_apply]

theorem lie_u1_u2 : ⁅u1, u2⁆ = (-2 : ℝ) • zPlus := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [u1, u2, zPlus, generator, matrixOfCoordinates,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_succ,
      Pi.single_apply]

theorem lie_v1_v2 : ⁅v1, v2⁆ = (2 : ℝ) • zMinus := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [v1, v2, zMinus, generator, matrixOfCoordinates,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_succ,
      Pi.single_apply]

theorem lie_zPlus_zMinus : ⁅zPlus, zMinus⁆ = gradingElement := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zPlus, zMinus, gradingElement, generator, matrixOfCoordinates,
      LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_succ,
      Pi.single_apply]

theorem lie_endpoint_brackets :
    ⁅⁅u1, u2⁆, ⁅v1, v2⁆⁆ = (-4 : ℝ) • gradingElement := by
  rw [lie_u1_u2, lie_v1_v2, smul_lie, lie_smul, lie_zPlus_zMinus, smul_smul]
  norm_num

theorem generator_ne_zero (i : Fin 10) : generator i ≠ 0 := by
  intro h
  have hc := congrArg (fun X : Sp => coordinates X i) h
  simp [generator, ← coordinateEquiv_symm_apply] at hc

theorem lie_u1_u2_ne_zero : ⁅u1, u2⁆ ≠ 0 := by
  rw [lie_u1_u2]
  exact smul_ne_zero (by norm_num) (generator_ne_zero 9)

/-- The nonzero Lie bracket also witnesses ordered matrix noncommutativity. -/
theorem u1_mul_u2_ne : (u1 : Mat) * (u2 : Mat) ≠ (u2 : Mat) * (u1 : Mat) := by
  intro h
  apply lie_u1_u2_ne_zero
  apply Subtype.ext
  change (u1 : Mat) * (u2 : Mat) - (u2 : Mat) * (u1 : Mat) = 0
  exact sub_eq_zero.mpr h

/-- Closed noncommutativity witness on the full native matrix carrier. -/
theorem exists_noncommuting_matrices :
    ∃ X Y : Matrix (Fin 4) (Fin 4) ℝ, X * Y ≠ Y * X :=
  ⟨(u1 : Mat), (u2 : Mat), u1_mul_u2_ne⟩

theorem lie_zPlus_zMinus_ne_zero : ⁅zPlus, zMinus⁆ ≠ 0 := by
  rw [lie_zPlus_zMinus]
  exact generator_ne_zero 3

end InfoGeometry.Algebra.Sp4Contact
