/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Real finite-dimensional Clifford kinetic and mass matrices

Explicit real matrix models for the `d = 1, 2, 3` kinetic generators and their
skew mass extensions. These are finite-dimensional algebraic results; they do
not assert the Atiyah--Bott--Shapiro classification of connected components.

The tensor order is Mathlib's standard Kronecker order. Thus the corrected
three-dimensional kinetic matrices are `σz ⊗ 1`, `σx ⊗ σz`, `σx ⊗ σx`;
the second mass is `σx ⊗ J`.
-/

namespace InfoGeometry.Clifford.RealDiracMassExtensions

open Matrix
open scoped Kronecker

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat4R := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ

/-- Algebraic mass-rotation identity in an arbitrary ring. Centrality of the
two coefficients is stated explicitly; this theorem makes no commutativity
assumption on the matrices `X` and `Y`. -/
theorem anticommuting_rotor_square {R : Type*} [Ring R]
    (X Y c s : R)
    (hX : X * X = -1) (hY : Y * Y = -1)
    (hXY : X * Y + Y * X = 0)
    (hcX : c * X = X * c) (hcY : c * Y = Y * c)
    (hsX : s * X = X * s) (hsY : s * Y = Y * s)
    (hcs : c * s = s * c) :
    (c * X + s * Y) * (c * X + s * Y) = -(c * c + s * s) := by
  have hXX : (c * X) * (c * X) = c * c * (X * X) := by
    calc
      (c * X) * (c * X) = c * (X * c) * X := by noncomm_ring
      _ = c * (c * X) * X := by rw [← hcX]
      _ = c * c * (X * X) := by noncomm_ring
  have hXY' : (c * X) * (s * Y) = c * s * (X * Y) := by
    calc
      (c * X) * (s * Y) = c * (X * s) * Y := by noncomm_ring
      _ = c * (s * X) * Y := by rw [← hsX]
      _ = c * s * (X * Y) := by noncomm_ring
  have hYX' : (s * Y) * (c * X) = c * s * (Y * X) := by
    calc
      (s * Y) * (c * X) = s * (Y * c) * X := by noncomm_ring
      _ = s * (c * Y) * X := by rw [← hcY]
      _ = s * c * (Y * X) := by noncomm_ring
      _ = c * s * (Y * X) := by rw [hcs.symm]
  have hYY : (s * Y) * (s * Y) = s * s * (Y * Y) := by
    calc
      (s * Y) * (s * Y) = s * (Y * s) * Y := by noncomm_ring
      _ = s * (s * Y) * Y := by rw [← hsY]
      _ = s * s * (Y * Y) := by noncomm_ring
  calc
    (c * X + s * Y) * (c * X + s * Y) =
        (c * X) * (c * X) + (c * X) * (s * Y) +
          (s * Y) * (c * X) + (s * Y) * (s * Y) := by noncomm_ring
    _ = c * c * (X * X) + c * s * (X * Y) +
          c * s * (Y * X) + s * s * (Y * Y) := by rw [hXX, hXY', hYX', hYY]
    _ = c * c * (X * X) + c * s * (X * Y + Y * X) +
          s * s * (Y * Y) := by noncomm_ring
    _ = -(c * c + s * s) := by
      rw [hX, hY, hXY]
      noncomm_ring

def sigmaZ : Mat2R := !![1, 0; 0, -1]
def sigmaX : Mat2R := !![0, 1; 1, 0]
def massJ : Mat2R := !![0, 1; -1, 0]

theorem pauli_real_relations :
    sigmaZ.transpose = sigmaZ ∧ sigmaX.transpose = sigmaX ∧
    massJ.transpose = -massJ ∧
    sigmaZ * sigmaZ = 1 ∧ sigmaX * sigmaX = 1 ∧ massJ * massJ = -1 ∧
    sigmaZ * sigmaX + sigmaX * sigmaZ = 0 ∧
    sigmaZ * massJ + massJ * sigmaZ = 0 ∧
    sigmaX * massJ + massJ * sigmaX = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [sigmaZ, sigmaX, massJ, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.transpose_apply, Matrix.neg_apply])

def gamma1_3 : Mat4R := sigmaZ ⊗ₖ (1 : Mat2R)
def gamma2_3 : Mat4R := sigmaX ⊗ₖ sigmaZ
def gamma3_3 : Mat4R := sigmaX ⊗ₖ sigmaX
def mass1_3 : Mat4R := massJ ⊗ₖ (1 : Mat2R)
def mass2_3 : Mat4R := sigmaX ⊗ₖ massJ

def gamma2_2D : Mat4R := sigmaX ⊗ₖ (1 : Mat2R)
def massPM_2D : Mat4R := massJ ⊗ₖ sigmaZ
def massSym_2D : Mat4R := massJ ⊗ₖ sigmaX

/-- Circular interpolation of the two skew masses in the `d = 3` model. -/
def massRotor3 (c s : ℝ) : Mat4R := c • mass1_3 + s • mass2_3

/-- A Clifford anticommutator vanishes when precisely one tensor factor
anticommutes and the other pair commutes. -/
private theorem kronecker_anticommute_left
    (A C B D : Mat2R) (hAC : A * C + C * A = 0)
    (hBD : D * B = B * D) :
    (A ⊗ₖ B) * (C ⊗ₖ D) + (C ⊗ₖ D) * (A ⊗ₖ B) = 0 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hBD,
    ← Matrix.add_kronecker, hAC]
  simp

private theorem kronecker_anticommute_right
    (A C B D : Mat2R) (hAC : C * A = A * C)
    (hBD : B * D + D * B = 0) :
    (A ⊗ₖ B) * (C ⊗ₖ D) + (C ⊗ₖ D) * (A ⊗ₖ B) = 0 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hAC,
    ← Matrix.kronecker_add, hBD]
  simp

private theorem kronecker_neg_left (A B : Mat2R) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.kroneckerMap_apply]

private theorem kronecker_neg_right (A B : Mat2R) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.kroneckerMap_apply]

private theorem kron_one_one :
    (1 : Mat2R) ⊗ₖ (1 : Mat2R) = (1 : Mat4R) :=
  Matrix.one_kronecker_one

private theorem kron_neg_one_left :
    (-1 : Mat2R) ⊗ₖ (1 : Mat2R) = -(1 : Mat4R) := by
  calc
    (-1 : Mat2R) ⊗ₖ (1 : Mat2R) = -((1 : Mat2R) ⊗ₖ (1 : Mat2R)) := by
      exact kronecker_neg_left 1 1
    _ = -(1 : Mat4R) := congrArg Neg.neg kron_one_one

private theorem kron_one_neg_one :
    (1 : Mat2R) ⊗ₖ (-1 : Mat2R) = -(1 : Mat4R) := by
  calc
    (1 : Mat2R) ⊗ₖ (-1 : Mat2R) = -((1 : Mat2R) ⊗ₖ (1 : Mat2R)) := by
      exact kronecker_neg_right 1 1
    _ = -(1 : Mat4R) := congrArg Neg.neg kron_one_one

theorem gamma3_clifford_mass_relations :
    gamma1_3.transpose = gamma1_3 ∧ gamma2_3.transpose = gamma2_3 ∧
    gamma3_3.transpose = gamma3_3 ∧
    gamma1_3 * gamma1_3 = 1 ∧ gamma2_3 * gamma2_3 = 1 ∧
    gamma3_3 * gamma3_3 = 1 ∧
    gamma1_3 * gamma2_3 + gamma2_3 * gamma1_3 = 0 ∧
    gamma1_3 * gamma3_3 + gamma3_3 * gamma1_3 = 0 ∧
    gamma2_3 * gamma3_3 + gamma3_3 * gamma2_3 = 0 ∧
    mass1_3.transpose = -mass1_3 ∧ mass2_3.transpose = -mass2_3 ∧
    mass1_3 * mass1_3 = -1 ∧ mass2_3 * mass2_3 = -1 ∧
    gamma1_3 * mass1_3 + mass1_3 * gamma1_3 = 0 ∧
    gamma2_3 * mass1_3 + mass1_3 * gamma2_3 = 0 ∧
    gamma3_3 * mass1_3 + mass1_3 * gamma3_3 = 0 ∧
    gamma1_3 * mass2_3 + mass2_3 * gamma1_3 = 0 ∧
    gamma2_3 * mass2_3 + mass2_3 * gamma2_3 = 0 ∧
    gamma3_3 * mass2_3 + mass2_3 * gamma3_3 = 0 ∧
    mass1_3 * mass2_3 + mass2_3 * mass1_3 = 0 := by
  rcases pauli_real_relations with ⟨hzT, hxT, hjT, hz2, hx2, hj2,
    hzx, hzj, hxj⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · change (sigmaZ ⊗ₖ (1 : Mat2R))ᵀ = sigmaZ ⊗ₖ (1 : Mat2R)
    rw [← Matrix.kroneckerMap_transpose, hzT, Matrix.transpose_one]
  · change (sigmaX ⊗ₖ sigmaZ)ᵀ = sigmaX ⊗ₖ sigmaZ
    rw [← Matrix.kroneckerMap_transpose, hxT, hzT]
  · change (sigmaX ⊗ₖ sigmaX)ᵀ = sigmaX ⊗ₖ sigmaX
    rw [← Matrix.kroneckerMap_transpose, hxT]
  · change (sigmaZ ⊗ₖ (1 : Mat2R)) * (sigmaZ ⊗ₖ (1 : Mat2R)) = 1
    rw [← Matrix.mul_kronecker_mul, hz2, Matrix.one_mul]
    exact kron_one_one
  · change (sigmaX ⊗ₖ sigmaZ) * (sigmaX ⊗ₖ sigmaZ) = 1
    rw [← Matrix.mul_kronecker_mul, hx2, hz2]
    exact kron_one_one
  · change (sigmaX ⊗ₖ sigmaX) * (sigmaX ⊗ₖ sigmaX) = 1
    rw [← Matrix.mul_kronecker_mul, hx2]
    exact kron_one_one
  · exact kronecker_anticommute_left sigmaZ sigmaX 1 sigmaZ hzx (by simp)
  · exact kronecker_anticommute_left sigmaZ sigmaX 1 sigmaX hzx (by simp)
  · exact kronecker_anticommute_right sigmaX sigmaX sigmaZ sigmaX (by simp) hzx
  · change (massJ ⊗ₖ (1 : Mat2R))ᵀ = -(massJ ⊗ₖ (1 : Mat2R))
    rw [← Matrix.kroneckerMap_transpose, hjT, Matrix.transpose_one]
    exact kronecker_neg_left massJ 1
  · change (sigmaX ⊗ₖ massJ)ᵀ = -(sigmaX ⊗ₖ massJ)
    rw [← Matrix.kroneckerMap_transpose, hxT, hjT]
    exact kronecker_neg_right sigmaX massJ
  · change (massJ ⊗ₖ (1 : Mat2R)) * (massJ ⊗ₖ (1 : Mat2R)) = -1
    rw [← Matrix.mul_kronecker_mul, hj2, Matrix.one_mul]
    exact kron_neg_one_left
  · change (sigmaX ⊗ₖ massJ) * (sigmaX ⊗ₖ massJ) = -1
    rw [← Matrix.mul_kronecker_mul, hx2, hj2]
    exact kron_one_neg_one
  · exact kronecker_anticommute_left sigmaZ massJ 1 1 hzj (by simp)
  · exact kronecker_anticommute_left sigmaX massJ sigmaZ 1 hxj (by simp)
  · exact kronecker_anticommute_left sigmaX massJ sigmaX 1 hxj (by simp)
  · exact kronecker_anticommute_left sigmaZ sigmaX 1 massJ hzx (by simp)
  · exact kronecker_anticommute_right sigmaX sigmaX sigmaZ massJ (by simp) hzj
  · exact kronecker_anticommute_right sigmaX sigmaX sigmaX massJ (by simp) hxj
  · exact kronecker_anticommute_left massJ sigmaX 1 massJ
      (by simpa [add_comm] using hxj) (by simp)

/-- The two anticommuting masses give a gap-preserving circular path from
`mass1_3` to its negative whenever `c²+s²=1`. This is a finite-matrix path
identity, not by itself a claim about the stable classification group. -/
theorem mass_rotor3_unit_gap (c s : ℝ) (hnorm : c * c + s * s = 1) :
    massRotor3 c s * massRotor3 c s = -(1 : Mat4R) := by
  rcases gamma3_clifford_mass_relations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hXsq, hYsq,
      _, _, _, _, _, _, hXY⟩
  let C : Mat4R := c • (1 : Mat4R)
  let S : Mat4R := s • (1 : Mat4R)
  have hCX : C * mass1_3 = mass1_3 * C := by
    dsimp [C]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hCY : C * mass2_3 = mass2_3 * C := by
    dsimp [C]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hSX : S * mass1_3 = mass1_3 * S := by
    dsimp [S]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hSY : S * mass2_3 = mass2_3 * S := by
    dsimp [S]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hCS : C * S = S * C := by
    dsimp [C, S]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      one_mul, mul_one, mul_comm]
  have hcore := anticommuting_rotor_square mass1_3 mass2_3 C S
    hXsq hYsq hXY hCX hCY hSX hSY hCS
  have hscalar : C * C + S * S = (c * c + s * s) • (1 : Mat4R) := by
    dsimp [C, S]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      one_mul, mul_one]
    rw [← add_smul]
  calc
    massRotor3 c s * massRotor3 c s = (C * mass1_3 + S * mass2_3) *
        (C * mass1_3 + S * mass2_3) := by
          simp [massRotor3, C, S, Matrix.smul_mul, Matrix.mul_smul,
            one_mul, mul_one]
    _ = -(C * C + S * S) := hcore
    _ = -((c * c + s * s) • (1 : Mat4R)) := by rw [hscalar]
    _ = -(1 : Mat4R) := by rw [hnorm]; simp

/-- In two spatial dimensions, the allowed symmetric multiplicity factors
`σz` and `σx` give opposite-sign and cancelling mass sectors. -/
theorem gamma2_clifford_mass_relations :
    massPM_2D.transpose = -massPM_2D ∧
    massSym_2D.transpose = -massSym_2D ∧
    massPM_2D * massPM_2D = -1 ∧
    massSym_2D * massSym_2D = -1 ∧
    gamma1_3 * massPM_2D + massPM_2D * gamma1_3 = 0 ∧
    gamma1_3 * massSym_2D + massSym_2D * gamma1_3 = 0 ∧
    gamma2_2D * massPM_2D + massPM_2D * gamma2_2D = 0 ∧
    gamma2_2D * massSym_2D + massSym_2D * gamma2_2D = 0 ∧
    massPM_2D * massSym_2D + massSym_2D * massPM_2D = 0 := by
  rcases pauli_real_relations with ⟨hzT, hxT, hjT, hz2, hx2, hj2,
    hzx, hzj, hxj⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (massJ ⊗ₖ sigmaZ)ᵀ = -(massJ ⊗ₖ sigmaZ)
    rw [← Matrix.kroneckerMap_transpose, hjT, hzT]
    exact kronecker_neg_left massJ sigmaZ
  · change (massJ ⊗ₖ sigmaX)ᵀ = -(massJ ⊗ₖ sigmaX)
    rw [← Matrix.kroneckerMap_transpose, hjT, hxT]
    exact kronecker_neg_left massJ sigmaX
  · change (massJ ⊗ₖ sigmaZ) * (massJ ⊗ₖ sigmaZ) = -1
    rw [← Matrix.mul_kronecker_mul, hj2, hz2]
    exact kron_neg_one_left
  · change (massJ ⊗ₖ sigmaX) * (massJ ⊗ₖ sigmaX) = -1
    rw [← Matrix.mul_kronecker_mul, hj2, hx2]
    exact kron_neg_one_left
  · exact kronecker_anticommute_left sigmaZ massJ 1 sigmaZ hzj (by simp)
  · exact kronecker_anticommute_left sigmaZ massJ 1 sigmaX hzj (by simp)
  · exact kronecker_anticommute_left sigmaX massJ 1 sigmaZ hxj (by simp)
  · exact kronecker_anticommute_left sigmaX massJ 1 sigmaX hxj (by simp)
  · exact kronecker_anticommute_right massJ massJ sigmaZ sigmaX
      (by simp) hzx

/-- Exact finite-matrix DIII-style relations for the chosen real factor:
it is skew and squares to `-1`, anticommutes with all three kinetic matrices,
and is compatible with the displayed `mass2_3`. It is only a real matrix
factor, not the full complex antiunitary operator; this is a matrix identity,
not a stable classification theorem. -/
theorem timeReversalFactor3_relations :
    mass2_3.transpose = -mass2_3 ∧
    mass2_3 * mass2_3 = -1 ∧
    gamma1_3 * mass2_3 + mass2_3 * gamma1_3 = 0 ∧
    gamma2_3 * mass2_3 + mass2_3 * gamma2_3 = 0 ∧
    gamma3_3 * mass2_3 + mass2_3 * gamma3_3 = 0 ∧
    mass2_3 * mass2_3 - mass2_3 * mass2_3 = 0 := by
  rcases gamma3_clifford_mass_relations with
    ⟨_, _, _, _, _, _, _, _, _, _, hMass2T, _, hMass2Sq,
      _, _, _, hGamma1M2, hGamma2M2, hGamma3M2, _⟩
  exact ⟨hMass2T, hMass2Sq, hGamma1M2, hGamma2M2, hGamma3M2, sub_self _⟩

end InfoGeometry.Clifford.RealDiracMassExtensions
