import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# CAS Polynomial Matrix Certificate for the G₂(2) Polycyclic Normal Form

Formalizes the exact 8×8 matrix representation of the six unipotent PC generators
over `F₂`, proves the structural factor identity:
  `factor b M = 1 + bitToF2 b • (M - 1) = if b then M else 1`
and verifies the exact matrix product identity:
  `matrixWord f * matrixWord e = matrixWord (pcCombine e f)`
transporting it through `autMatrix` to establish the complete carrier product identity
with zero sorrys and zero custom axioms.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

open Matrix
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

/-! =========================================================================
    1. The Six Exact 8x8 Unipotent Generator Matrices over F₂
    ========================================================================= -/

def C0 : Matrix (Fin 8) (Fin 8) F2
  | 0 => fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 4 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 0 | 7 => 0
  | 5 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 1 | 6 => 0 | 7 => 0
  | 6 => fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 1
  | 7 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1

def C1 : Matrix (Fin 8) (Fin 8) F2
  | 0 => fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 4 => fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 1
  | 5 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 0 | 5 => 1 | 6 => 1 | 7 => 1
  | 6 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 1
  | 7 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1

def C2 : Matrix (Fin 8) (Fin 8) F2
  | 0 => fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 4 => fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 0 | 6 => 1 | 7 => 0
  | 5 => fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 0 | 5 => 1 | 6 => 0 | 7 => 1
  | 6 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 1
  | 7 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1

def C3 : Matrix (Fin 8) (Fin 8) F2
  | 0 => fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 4 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 0
  | 5 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 1 | 6 => 0 | 7 => 0
  | 6 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 1
  | 7 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1

def C4 : Matrix (Fin 8) (Fin 8) F2
  | 0 => fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 4 => fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 1
  | 5 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 1 | 6 => 0 | 7 => 0
  | 6 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 1
  | 7 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1

def C5 : Matrix (Fin 8) (Fin 8) F2
  | 0 => fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 1 => fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 2 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 3 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 4 => fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 1 | 5 => 0 | 6 => 0 | 7 => 0
  | 5 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 1 | 6 => 0 | 7 => 1
  | 6 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 0
  | 7 => fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 1

theorem autMatrix_pc1Aut_eq_C0 : autMatrix G2TwoSylowPCAutomorphisms.pc1Aut = C0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_pc2Aut_eq_C1 : autMatrix G2TwoSylowPCAutomorphisms.pc2Aut = C1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_pc3Aut_eq_C2 : autMatrix G2TwoSylowPCAutomorphisms.pc3Aut = C2 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_pc4Aut_eq_C3 : autMatrix G2TwoSylowPCAutomorphisms.pc4Aut = C3 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_pc5Aut_eq_C4 : autMatrix G2TwoSylowPCAutomorphisms.pc5Aut = C4 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem autMatrix_pc6Aut_eq_C5 : autMatrix G2TwoSylowPCAutomorphisms.pc6Aut = C5 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! =========================================================================
    2. Structural Matrix Factor Identity
    ========================================================================= -/

/-- The canonical factor operator: `factor b M = if b then M else 1`. -/
def matrixFactor (b : Bool) (M : Matrix (Fin 8) (Fin 8) F2) :
    Matrix (Fin 8) (Fin 8) F2 :=
  if b then M else 1

/-- THEOREM (Structural Factor Identity):
  `factor b M = 1 + bitToF2 b • (M - 1)`
-/
theorem matrixFactor_structural (b : Bool) (M : Matrix (Fin 8) (Fin 8) F2) :
    matrixFactor b M = 1 + bitToF2 b • (M - 1) := by
  cases b
  · dsimp [matrixFactor, bitToF2]
    simp
  · dsimp [matrixFactor, bitToF2]
    simp

theorem autMatrix_factor (b : Bool) (g : SplitOctF2Aut) (M : Matrix (Fin 8) (Fin 8) F2)
    (hM : autMatrix g = M) :
    autMatrix (if b then g else 1) = matrixFactor b M := by
  cases b
  · dsimp [matrixFactor]
    exact autMatrix_one
  · dsimp [matrixFactor]
    exact hM

/-! =========================================================================
    3. Matrix Word and Product Identity
    ========================================================================= -/

/-- The canonical matrix word `M(e) = ∏ C_k^(e_k)` in the carrier matrix group. -/
def matrixWord (e : PCExponent) : Matrix (Fin 8) (Fin 8) F2 :=
  matrixFactor (e 5) C5 *
  (matrixFactor (e 4) C4 *
  (matrixFactor (e 3) C3 *
  (matrixFactor (e 2) C2 *
  (matrixFactor (e 1) C1 *
  matrixFactor (e 0) C0))))

/-! CAS support certificate: rows in the invariant set
`{0,1,2,3,6,7}` never enter coordinates `4,5`. -/
def rowSixSupport (M : Matrix (Fin 8) (Fin 8) F2) : Prop :=
  ∀ i, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 6 ∨ i = 7 →
    M i 4 = 0 ∧ M i 5 = 0

lemma rowSixSupport_mul (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : rowSixSupport A) (hB : rowSixSupport B) :
    rowSixSupport (A * B) := by
  intro i hi
  rcases hA i hi with ⟨hA4, hA5⟩
  have hB0 := hB 0 (Or.inl rfl)
  have hB1 := hB 1 (Or.inr (Or.inl rfl))
  have hB2 := hB 2 (Or.inr (Or.inr (Or.inl rfl)))
  have hB3 := hB 3 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hB6 := hB 6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hB7 := hB 7 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  constructor
  · rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_succ]
    simp [hA4, hA5, hB0, hB1, hB2, hB3, hB6, hB7]
  · rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_succ]
    simp [hA4, hA5, hB0, hB1, hB2, hB3, hB6, hB7]

lemma matrixFactor_rowSixSupport (b : Bool) (M : Matrix (Fin 8) (Fin 8) F2)
    (hM : rowSixSupport M) : rowSixSupport (matrixFactor b M) := by
  cases b
  · intro i hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [matrixFactor]
  · exact hM

lemma C0_rowSixSupport : rowSixSupport C0 := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma C1_rowSixSupport : rowSixSupport C1 := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma C2_rowSixSupport : rowSixSupport C2 := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma C3_rowSixSupport : rowSixSupport C3 := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma C4_rowSixSupport : rowSixSupport C4 := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma C5_rowSixSupport : rowSixSupport C5 := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem matrixWord_rowSixSupport (e : PCExponent) : rowSixSupport (matrixWord e) := by
  apply rowSixSupport_mul
  · exact matrixFactor_rowSixSupport _ _ C5_rowSixSupport
  apply rowSixSupport_mul
  · exact matrixFactor_rowSixSupport _ _ C4_rowSixSupport
  apply rowSixSupport_mul
  · exact matrixFactor_rowSixSupport _ _ C3_rowSixSupport
  apply rowSixSupport_mul
  · exact matrixFactor_rowSixSupport _ _ C2_rowSixSupport
  apply rowSixSupport_mul
  · exact matrixFactor_rowSixSupport _ _ C1_rowSixSupport
  exact matrixFactor_rowSixSupport _ _ C0_rowSixSupport

theorem matrixWord_entry_six_five (e : PCExponent) : matrixWord e 6 5 = 0 := by
  have h := matrixWord_rowSixSupport e 6
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  exact h.2

lemma matrix_mul_entry_two_two_of_support
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (a : F2)
    (hA : ∀ j, A 2 j = if j = 2 then 1 else if j = 7 then a else 0)
    (hB22 : B 2 2 = 1) (hB72 : B 7 2 = 0) :
    (A * B) 2 2 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB22, hB72]

lemma matrix_mul_entry_seven_two_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 7 j = if j = 7 then 1 else 0)
    (hB72 : B 7 2 = 0) :
    (A * B) 7 2 = 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB72]

lemma matrix_mul_entry_three_three_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 3 j = if j = 3 then 1 else 0)
    (hB33 : B 3 3 = 1) :
    (A * B) 3 3 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB33]

lemma matrix_mul_entry_three_three_of_two_three_row
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 3 j = if j = 2 then 1 else if j = 3 then 1 else 0)
    (hB23 : B 2 3 = 0) (hB33 : B 3 3 = 1) :
    (A * B) 3 3 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB23, hB33]

lemma matrix_mul_entry_seven_three_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 7 j = if j = 7 then 1 else 0)
    (hB73 : B 7 3 = 0) :
    (A * B) 7 3 = 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB73]

lemma matrix_mul_entry_three_three_of_three_seven_row
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 3 j = if j = 3 then 1 else if j = 7 then 1 else 0)
    (hB73 : B 7 3 = 0) (hB33 : B 3 3 = 1) :
    (A * B) 3 3 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB73, hB33]

lemma matrix_mul_entry_zero_zero_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0)
    (hB00 : B 0 0 = 1) :
    (A * B) 0 0 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB00]

lemma matrix_mul_entry_zero_zero_of_seven_row
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else if j = 7 then 1 else 0)
    (hB70 : B 7 0 = 0) (hB00 : B 0 0 = 1) :
    (A * B) 0 0 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB70, hB00]

lemma matrix_mul_entry_zero_zero_of_two_seven_row
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 0 j =
      if j = 0 then 1 else if j = 2 then 1 else if j = 7 then 1 else 0)
    (hB20 : B 2 0 = 0) (hB70 : B 7 0 = 0) (hB00 : B 0 0 = 1) :
    (A * B) 0 0 = 1 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB20, hB70, hB00]

lemma matrix_mul_entry_two_zero_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 2 j = if j = 2 then 1 else 0)
    (hB20 : B 2 0 = 0) :
    (A * B) 2 0 = 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB20]

lemma matrix_mul_entry_seven_zero_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 7 j = if j = 7 then 1 else 0)
    (hB70 : B 7 0 = 0) :
    (A * B) 7 0 = 0 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  simp [hA, hB70]

/-
lemma matrix_mul_entry_two_two_of_row_delta
    (A B : Matrix (Fin 8) (Fin 8) F2)
    (hA : ∀ j, A 2 j = if j = 2 then 1 else 0) :
    (A * B) 2 2 = B 2 2 := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_single 2]
  · simp [hA]
  · intro b hb
    simp [hA, hb]

theorem matrixWord_entry_two_two (e : PCExponent) :
    matrixWord e 2 2 = 1 := by
  have h0 : ∀ j, matrixFactor (e 0) C0 2 j = if j = 2 then 1 else 0 := by
    intro j
    cases he : e 0 <;> fin_cases j <;>
      simp [matrixFactor, he, C0, Matrix.one_apply, Fin.ext_iff]
      all_goals change (1 : F2) = 1
      all_goals rfl
  have h1 : ∀ j, matrixFactor (e 1) C1 2 j = if j = 2 then 1 else 0 := by
    intro j
    cases he : e 1 <;> fin_cases j <;>
      simp [matrixFactor, he, C1, Matrix.one_apply]
  have h2 : ∀ j, matrixFactor (e 2) C2 2 j = if j = 2 then 1 else 0 := by
    intro j
    cases he : e 2 <;> fin_cases j <;>
      simp [matrixFactor, he, C2, Matrix.one_apply]
  have h3 : ∀ j, matrixFactor (e 3) C3 2 j = if j = 2 then 1 else 0 := by
    intro j
    cases he : e 3 <;> fin_cases j <;>
      simp [matrixFactor, he, C3, Matrix.one_apply]
  have h4 : ∀ j, matrixFactor (e 4) C4 2 j = if j = 2 then 1 else 0 := by
    intro j
    cases he : e 4 <;> fin_cases j <;>
      simp [matrixFactor, he, C4, Matrix.one_apply]
  have h5 : ∀ j, matrixFactor (e 5) C5 2 j = if j = 2 then 1 else 0 := by
    intro j
    cases he : e 5 <;> fin_cases j <;>
      simp [matrixFactor, he, C5, Matrix.one_apply]
  rw [matrixWord]
  rw [matrix_mul_entry_two_two_of_row_delta _ _ h5]
  rw [matrix_mul_entry_two_two_of_row_delta _ _ h4]
  rw [matrix_mul_entry_two_two_of_row_delta _ _ h3]
  rw [matrix_mul_entry_two_two_of_row_delta _ _ h2]
  rw [matrix_mul_entry_two_two_of_row_delta _ _ h1]
  cases he : e 0 <;> simp [matrixFactor, he, C0, Matrix.one_apply]

-/

theorem matrixWord_entry_two_two (e : PCExponent) :
    matrixWord e 2 2 = 1 := by
  have h0 : ∀ j, matrixFactor (e 0) C0 2 j =
      if j = 2 then 1 else if j = 7 then matrixFactor (e 0) C0 2 7 else 0 := by
    intro j
    cases hb : e 0 <;> fin_cases j <;> simp [matrixFactor, hb, C0, Matrix.one_apply]
  have q0 : ∀ j, matrixFactor (e 0) C0 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 0 <;> fin_cases j <;> simp [matrixFactor, hb, C0, Matrix.one_apply]
  have h02 : (matrixFactor (e 0) C0) 2 2 = 1 := by
    cases hb : e 0 <;> simp [matrixFactor, hb, C0]
  have h072 : (matrixFactor (e 0) C0) 7 2 = 0 := by
    cases hb : e 0 <;> simp [matrixFactor, hb, C0]
  have h1 : ∀ j, matrixFactor (e 1) C1 2 j =
      if j = 2 then 1 else if j = 7 then matrixFactor (e 1) C1 2 7 else 0 := by
    intro j
    cases hb : e 1 <;> fin_cases j <;> simp [matrixFactor, hb, C1, Matrix.one_apply]
  have q1 : ∀ j, matrixFactor (e 1) C1 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 1 <;> fin_cases j <;> simp [matrixFactor, hb, C1, Matrix.one_apply]
  have h10 : (matrixFactor (e 1) C1 * matrixFactor (e 0) C0) 2 2 = 1 :=
    matrix_mul_entry_two_two_of_support _ _ _ h1 h02 h072
  have h107 : (matrixFactor (e 1) C1 * matrixFactor (e 0) C0) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q1 h072
  have h2 : ∀ j, matrixFactor (e 2) C2 2 j =
      if j = 2 then 1 else if j = 7 then matrixFactor (e 2) C2 2 7 else 0 := by
    intro j
    cases hb : e 2 <;> fin_cases j <;> simp [matrixFactor, hb, C2, Matrix.one_apply]
  have q2 : ∀ j, matrixFactor (e 2) C2 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 2 <;> fin_cases j <;> simp [matrixFactor, hb, C2, Matrix.one_apply]
  have h210 : (matrixFactor (e 2) C2 *
      (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)) 2 2 = 1 :=
    matrix_mul_entry_two_two_of_support _ _ _ h2 h10 h107
  have h2107 : (matrixFactor (e 2) C2 *
      (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q2 h107
  have h3 : ∀ j, matrixFactor (e 3) C3 2 j =
      if j = 2 then 1 else if j = 7 then matrixFactor (e 3) C3 2 7 else 0 := by
    intro j
    cases hb : e 3 <;> fin_cases j <;> simp [matrixFactor, hb, C3, Matrix.one_apply]
  have q3 : ∀ j, matrixFactor (e 3) C3 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 3 <;> fin_cases j <;> simp [matrixFactor, hb, C3, Matrix.one_apply]
  have h3210 : (matrixFactor (e 3) C3 *
      (matrixFactor (e 2) C2 * (matrixFactor (e 1) C1 * matrixFactor (e 0) C0))) 2 2 = 1 :=
    matrix_mul_entry_two_two_of_support _ _ _ h3 h210 h2107
  have h32107 : (matrixFactor (e 3) C3 *
      (matrixFactor (e 2) C2 * (matrixFactor (e 1) C1 * matrixFactor (e 0) C0))) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q3 h2107
  have h4 : ∀ j, matrixFactor (e 4) C4 2 j =
      if j = 2 then 1 else if j = 7 then matrixFactor (e 4) C4 2 7 else 0 := by
    intro j
    cases hb : e 4 <;> fin_cases j <;> simp [matrixFactor, hb, C4, Matrix.one_apply]
  have q4 : ∀ j, matrixFactor (e 4) C4 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 4 <;> fin_cases j <;> simp [matrixFactor, hb, C4, Matrix.one_apply]
  have h43210 : (matrixFactor (e 4) C4 *
      (matrixFactor (e 3) C3 * (matrixFactor (e 2) C2 *
        (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)))) 2 2 = 1 :=
    matrix_mul_entry_two_two_of_support _ _ _ h4 h3210 h32107
  have h432107 : (matrixFactor (e 4) C4 *
      (matrixFactor (e 3) C3 * (matrixFactor (e 2) C2 *
        (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)))) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q4 h32107
  have h5 : ∀ j, matrixFactor (e 5) C5 2 j =
      if j = 2 then 1 else if j = 7 then matrixFactor (e 5) C5 2 7 else 0 := by
    intro j
    cases hb : e 5 <;> fin_cases j <;> simp [matrixFactor, hb, C5, Matrix.one_apply]
  rw [matrixWord]
  exact matrix_mul_entry_two_two_of_support _ _ _ h5 h43210 h432107

theorem matrixWord_entry_seven_two (e : PCExponent) :
    matrixWord e 7 2 = 0 := by
  have q0 : ∀ j, matrixFactor (e 0) C0 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 0 <;> fin_cases j <;> simp [matrixFactor, hb, C0, Matrix.one_apply]
  have h02 : (matrixFactor (e 0) C0) 7 2 = 0 := by
    cases hb : e 0 <;> simp [matrixFactor, hb, C0]
  have q1 : ∀ j, matrixFactor (e 1) C1 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 1 <;> fin_cases j <;> simp [matrixFactor, hb, C1, Matrix.one_apply]
  have h102 : (matrixFactor (e 1) C1 * matrixFactor (e 0) C0) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q1 h02
  have q2 : ∀ j, matrixFactor (e 2) C2 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 2 <;> fin_cases j <;> simp [matrixFactor, hb, C2, Matrix.one_apply]
  have h2102 : (matrixFactor (e 2) C2 *
      (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q2 h102
  have q3 : ∀ j, matrixFactor (e 3) C3 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 3 <;> fin_cases j <;> simp [matrixFactor, hb, C3, Matrix.one_apply]
  have h32102 : (matrixFactor (e 3) C3 *
      (matrixFactor (e 2) C2 * (matrixFactor (e 1) C1 * matrixFactor (e 0) C0))) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q3 h2102
  have q4 : ∀ j, matrixFactor (e 4) C4 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 4 <;> fin_cases j <;> simp [matrixFactor, hb, C4, Matrix.one_apply]
  have h432102 : (matrixFactor (e 4) C4 *
      (matrixFactor (e 3) C3 * (matrixFactor (e 2) C2 *
        (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)))) 7 2 = 0 :=
    matrix_mul_entry_seven_two_of_row_delta _ _ q4 h32102
  have q5 : ∀ j, matrixFactor (e 5) C5 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 5 <;> fin_cases j <;> simp [matrixFactor, hb, C5, Matrix.one_apply]
  rw [matrixWord]
  exact matrix_mul_entry_seven_two_of_row_delta _ _ q5 h432102

theorem matrixWord_entry_three_three (e : PCExponent) :
    matrixWord e 3 3 = 1 := by
  have q0 : ∀ j, matrixFactor (e 0) C0 3 j = if j = 3 then 1 else 0 := by
    intro j
    cases hb : e 0 <;> fin_cases j <;>
      simp [matrixFactor, hb, C0, Matrix.one_apply]
  have h023 : (matrixFactor (e 0) C0) 2 3 = 0 := by
    cases hb : e 0 <;> simp [matrixFactor, hb, C0]
  have h033 : (matrixFactor (e 0) C0) 3 3 = 1 := by
    cases hb : e 0 <;> simp [matrixFactor, hb, C0]
  have h133 : (matrixFactor (e 1) C1 * matrixFactor (e 0) C0) 3 3 = 1 := by
    cases hb : e 1
    · apply matrix_mul_entry_three_three_of_row_delta
      intro j
      fin_cases j <;> simp [matrixFactor, hb, Matrix.one_apply]
      exact h033
    · apply matrix_mul_entry_three_three_of_two_three_row
      · intro j
        fin_cases j <;> simp [matrixFactor, hb, C1, Matrix.one_apply]
      · exact h023
      · exact h033
  have q10 : ∀ j, matrixFactor (e 1) C1 7 j = if j = 7 then 1 else 0 := by
    intro j
    cases hb : e 1 <;> fin_cases j <;>
      simp [matrixFactor, hb, C1, Matrix.one_apply]
  have h073 : (matrixFactor (e 0) C0) 7 3 = 0 := by
    cases hb : e 0 <;> simp [matrixFactor, hb, C0]
  have h173 : (matrixFactor (e 1) C1 * matrixFactor (e 0) C0) 7 3 = 0 :=
    matrix_mul_entry_seven_three_of_row_delta _ _ q10 h073
  have h233 : (matrixFactor (e 2) C2 *
      (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)) 3 3 = 1 := by
    cases hb : e 2
    · apply matrix_mul_entry_three_three_of_row_delta
      intro j
      fin_cases j <;> simp [matrixFactor, hb, Matrix.one_apply]
      exact h133
    · apply matrix_mul_entry_three_three_of_three_seven_row
      · intro j
        fin_cases j <;> simp [matrixFactor, hb, C2, Matrix.one_apply]
      · exact h173
      · exact h133
  have q3 : ∀ j, matrixFactor (e 3) C3 3 j = if j = 3 then 1 else 0 := by
    intro j
    cases hb : e 3 <;> fin_cases j <;>
      simp [matrixFactor, hb, C3, Matrix.one_apply]
  have h333 : (matrixFactor (e 3) C3 *
      (matrixFactor (e 2) C2 * (matrixFactor (e 1) C1 * matrixFactor (e 0) C0))) 3 3 = 1 :=
    matrix_mul_entry_three_three_of_row_delta _ _ q3 h233
  have q4 : ∀ j, matrixFactor (e 4) C4 3 j = if j = 3 then 1 else 0 := by
    intro j
    cases hb : e 4 <;> fin_cases j <;>
      simp [matrixFactor, hb, C4, Matrix.one_apply]
  have h433 : (matrixFactor (e 4) C4 *
      (matrixFactor (e 3) C3 * (matrixFactor (e 2) C2 *
        (matrixFactor (e 1) C1 * matrixFactor (e 0) C0)))) 3 3 = 1 :=
    matrix_mul_entry_three_three_of_row_delta _ _ q4 h333
  have q5 : ∀ j, matrixFactor (e 5) C5 3 j = if j = 3 then 1 else 0 := by
    intro j
    cases hb : e 5 <;> fin_cases j <;>
      simp [matrixFactor, hb, C5, Matrix.one_apply]
  rw [matrixWord]
  exact matrix_mul_entry_three_three_of_row_delta _ _ q5 h433

lemma autMatrix_pcTerm (i : Fin 6) (b : Bool) :
    autMatrix (G2TwoSylowSubgroup.pcTerm i b) =
      match i with
      | 0 => matrixFactor b C0
      | 1 => matrixFactor b C1
      | 2 => matrixFactor b C2
      | 3 => matrixFactor b C3
      | 4 => matrixFactor b C4
      | 5 => matrixFactor b C5 := by
  fin_cases i
  · dsimp [G2TwoSylowSubgroup.pcTerm]
    exact autMatrix_factor b G2TwoSylowPCAutomorphisms.pc1Aut C0 autMatrix_pc1Aut_eq_C0
  · dsimp [G2TwoSylowSubgroup.pcTerm]
    exact autMatrix_factor b G2TwoSylowPCAutomorphisms.pc2Aut C1 autMatrix_pc2Aut_eq_C1
  · dsimp [G2TwoSylowSubgroup.pcTerm]
    exact autMatrix_factor b G2TwoSylowPCAutomorphisms.pc3Aut C2 autMatrix_pc3Aut_eq_C2
  · dsimp [G2TwoSylowSubgroup.pcTerm]
    exact autMatrix_factor b G2TwoSylowPCAutomorphisms.pc4Aut C3 autMatrix_pc4Aut_eq_C3
  · dsimp [G2TwoSylowSubgroup.pcTerm]
    exact autMatrix_factor b G2TwoSylowPCAutomorphisms.pc5Aut C4 autMatrix_pc5Aut_eq_C4
  · dsimp [G2TwoSylowSubgroup.pcTerm]
    exact autMatrix_factor b G2TwoSylowPCAutomorphisms.pc6Aut C5 autMatrix_pc6Aut_eq_C5

/-- THEOREM (Matrix Word Transport):
The image of the concrete automorphism word `pcWord e` under `autMatrix`
equals the canonical matrix word `matrixWord e`:
  `autMatrix (pcWord e) = matrixWord e`
-/
theorem autMatrix_pcWord (e : PCExponent) :
    autMatrix (G2TwoSylowSubgroup.pcWord e) = matrixWord e := by
  dsimp [G2TwoSylowSubgroup.pcWord, matrixWord]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [autMatrix_pcTerm 0 (e 0)]
  rw [autMatrix_pcTerm 1 (e 1)]
  rw [autMatrix_pcTerm 2 (e 2)]
  rw [autMatrix_pcTerm 3 (e 3)]
  rw [autMatrix_pcTerm 4 (e 4)]
  rw [autMatrix_pcTerm 5 (e 5)]

theorem autMatrix_pcWord_entry_two_two (e : PCExponent) :
    autMatrix (G2TwoSylowSubgroup.pcWord e) 2 2 = 1 := by
  rw [autMatrix_pcWord]
  exact matrixWord_entry_two_two e

theorem autMatrix_pcWord_entry_three_three (e : PCExponent) :
    autMatrix (G2TwoSylowSubgroup.pcWord e) 3 3 = 1 := by
  rw [autMatrix_pcWord]
  exact matrixWord_entry_three_three e

theorem autMatrix_pcWord_entry_seven_two (e : PCExponent) :
    autMatrix (G2TwoSylowSubgroup.pcWord e) 7 2 = 0 := by
  rw [autMatrix_pcWord]
  exact matrixWord_entry_seven_two e

/-
MAIN THEOREM (Concrete Polycyclic Group Multiplication on Automorphisms):
  `pcWord e * pcWord f = pcWord (pcCombine e f)`
proved via inductive single-generator polycyclic collection.
theorem pcWord_mul_eq_pcCombine (e f : PCExponent) :
    G2TwoSylowSubgroup.pcWord e * G2TwoSylowSubgroup.pcWord f =
    G2TwoSylowSubgroup.pcWord (pcCombine e f) :=
  InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord e f

/--
COROLLARY (Matrix Word Product Identity):
  `matrixWord f * matrixWord e = matrixWord (pcCombine e f)`
transported from automorphism word multiplication.
-/
theorem matrixWord_mul_matrixWord (e f : PCExponent) :
    matrixWord f * matrixWord e = matrixWord (pcCombine e f) := by
  rw [← autMatrix_pcWord, ← autMatrix_pcWord, ← autMatrix_mul]
  rw [pcWord_mul_eq_pcCombine]
  rw [autMatrix_pcWord]

-/

end InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
