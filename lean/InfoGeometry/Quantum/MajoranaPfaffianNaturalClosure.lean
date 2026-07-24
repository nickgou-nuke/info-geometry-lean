import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable section

namespace InfoGeometry
namespace MajoranaPfaffianNaturalClosure

open Matrix
open scoped BigOperators

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-!
# 1. The concrete split-Clifford representation

`splitPos` and `splitNeg` are the two real generators of the standard
two-dimensional representation of `Cl(1,1)`.
-/

def splitPos : M2R :=
  !![0, 1; 1, 0]

def splitNeg : M2R :=
  !![0, 1; -1, 0]

theorem splitPos_sq :
    splitPos * splitPos = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitPos, Matrix.mul_apply, Fin.sum_univ_two]

theorem splitNeg_sq :
    splitNeg * splitNeg = -(1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitNeg, Matrix.mul_apply, Fin.sum_univ_two]

theorem split_anticommute :
    splitPos * splitNeg + splitNeg * splitPos = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitPos, splitNeg]

/-!
# 2. The null basis and the CAR matrix units
-/

def annihilationR : M2R :=
  !![0, 1; 0, 0]

def creationR : M2R :=
  !![0, 0; 1, 0]

theorem annihilationR_eq_null :
    annihilationR = (2 : ℝ)⁻¹ • (splitPos + splitNeg) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [annihilationR, splitPos, splitNeg]

theorem creationR_eq_null :
    creationR = (2 : ℝ)⁻¹ • (splitPos - splitNeg) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [creationR, splitPos, splitNeg]

theorem annihilationR_sq :
    annihilationR * annihilationR = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilationR, Matrix.mul_apply, Fin.sum_univ_two]

theorem creationR_sq :
    creationR * creationR = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [creationR, Matrix.mul_apply, Fin.sum_univ_two]

theorem real_CAR :
    annihilationR * creationR + creationR * annihilationR = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [annihilationR, creationR]

/-!
# 3. Natural algebraic closure
-/

def splitProd : M2R :=
  splitPos * splitNeg

theorem splitProd_explicit :
    splitProd = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitProd, splitPos, splitNeg, Matrix.mul_apply, Fin.sum_univ_two]

@[ext]
structure SplitBasisCoords where
  cI : ℝ
  cP : ℝ
  cN : ℝ
  cPN : ℝ

def expandSplitCoords (c : SplitBasisCoords) : M2R :=
  c.cI • (1 : M2R) + c.cP • splitPos + c.cN • splitNeg + c.cPN • splitProd

def matrixToSplitCoords (M : M2R) : SplitBasisCoords :=
  { cI := (M 0 0 + M 1 1) / 2
    cP := (M 0 1 + M 1 0) / 2
    cN := (M 0 1 - M 1 0) / 2
    cPN := (M 1 1 - M 0 0) / 2 }

theorem expand_matrixToSplitCoords (M : M2R) :
    expandSplitCoords (matrixToSplitCoords M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expandSplitCoords, matrixToSplitCoords, splitPos, splitNeg, splitProd] <;>
    ring

theorem matrixToSplitCoords_expand (c : SplitBasisCoords) :
    matrixToSplitCoords (expandSplitCoords c) = c := by
  ext <;>
    simp [matrixToSplitCoords, expandSplitCoords, splitPos, splitNeg, splitProd] <;>
    ring

/-!
# 4. Complexified Majorana pair
-/

def majorana1 : M2C :=
  splitPos.map (algebraMap ℝ ℂ)

def majorana2 : M2C :=
  (-Complex.I) • splitNeg.map (algebraMap ℝ ℂ)

theorem majorana1_sq :
    majorana1 * majorana1 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana1, splitPos, Matrix.mul_apply, Fin.sum_univ_two]

theorem majorana2_sq :
    majorana2 * majorana2 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana2, splitNeg, Matrix.mul_apply, Fin.sum_univ_two]

theorem majorana_anticommute :
    majorana1 * majorana2 + majorana2 * majorana1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majorana1, majorana2, splitPos, splitNeg, Matrix.mul_apply, Fin.sum_univ_two]

/-!
# 5. Skew 2x2 BdG matrix, Pfaffian, and spectrum
-/

def bdg2 (m : ℝ) : M2R :=
  !![0, m; -m, 0]

def pfaffian2 (m : ℝ) : ℝ :=
  m

theorem bdg2_eq_smul_splitNeg (m : ℝ) :
    bdg2 m = m • splitNeg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdg2, splitNeg]

theorem det_bdg2 (m : ℝ) :
    (bdg2 m).det = (pfaffian2 m)^2 := by
  simp [bdg2, pfaffian2, Matrix.det_fin_two]
  ring

theorem det_bdg2_eq_zero_iff (m : ℝ) :
    (bdg2 m).det = 0 ↔ pfaffian2 m = 0 := by
  rw [det_bdg2 m]
  exact sq_eq_zero_iff

theorem pfaffian2_eq_zero_iff (m : ℝ) :
    pfaffian2 m = 0 ↔ m = 0 := by
  rfl

end MajoranaPfaffianNaturalClosure
end InfoGeometry
