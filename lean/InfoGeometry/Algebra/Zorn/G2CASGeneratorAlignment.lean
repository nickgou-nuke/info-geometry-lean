import InfoGeometry.Algebra.Zorn.G2LeanCarrierMatrixAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native alignment of the six CAS carrier generators

The CAS carrier uses six 8x8 matrices.  The words below are the exact
factorisations returned by GAP in the ordered Lean generating system
`pc0,...,pc5,swap01Aut,correctedT`.  Since `autMatrix` is contravariant, the
Lean words are written in reverse order.  The resulting matrix equalities are
checked natively, so this file does not import a CAS proposition as an axiom.
-/

namespace InfoGeometry.Algebra.Zorn.G2CASGeneratorAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2LeanCarrierMatrixAlignment

abbrev F2 := ZMod 2

def codeMatrix (c : Fin 8 → Nat) : Matrix (Fin 8) (Fin 8) F2 :=
  fun i j => if (c j / 2 ^ (i : Nat)) % 2 = 1 then 1 else 0

def code0 : Fin 8 → Nat := ![2, 1, 128, 64, 32, 16, 8, 4]
def code1 : Fin 8 → Nat := ![2, 1, 128, 192, 224, 24, 12, 4]
def code2 : Fin 8 → Nat := ![134, 133, 128, 68, 175, 211, 136, 4]
def code3 : Fin 8 → Nat := ![1, 2, 4, 8, 24, 32, 192, 128]
def code4 : Fin 8 → Nat := ![129, 130, 4, 8, 147, 40, 68, 128]
def code5 : Fin 8 → Nat := ![2, 1, 64, 32, 128, 8, 4, 16]

noncomputable def cas0 : SplitOctF2Aut := correctedT
noncomputable def cas1 : SplitOctF2Aut :=
  pcGenerator 3 * correctedT * swap01Aut * correctedT *
    (pcGenerator 1)⁻¹ * swap01Aut * pcGenerator 1 * correctedT
noncomputable def cas2 : SplitOctF2Aut :=
  pcGenerator 0 * correctedT * swap01Aut * pcGenerator 2 * correctedT *
    swap01Aut * correctedT * swap01Aut * (pcGenerator 1)⁻¹
noncomputable def cas3 : SplitOctF2Aut :=
  pcGenerator 3 * correctedT * swap01Aut * correctedT * pcGenerator 3
noncomputable def cas4 : SplitOctF2Aut :=
  correctedT * pcGenerator 2 * swap01Aut * correctedT * pcGenerator 2 *
    swap01Aut * pcGenerator 2 * correctedT
noncomputable def cas5 : SplitOctF2Aut :=
  correctedT * swap01Aut * correctedT * swap01Aut * correctedT

theorem cas0_matrix : autMatrix cas0 = codeMatrix code0 := by
  rw [cas0, autMatrix_correctedT_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 1000000 in
theorem cas1_matrix : autMatrix cas1 = codeMatrix code1 := by
  rw [cas1]
  simp only [pcGenerator.eq_def]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul,
    autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [pc2Aut_inv_eq, autMatrix_mul]
  rw [autMatrix_correctedT_eq, autMatrix_pc2Aut_eq,
    autMatrix_swap01Aut_eq, autMatrix_pc6Aut_eq, autMatrix_pc4Aut_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 1000000 in
theorem cas2_matrix : autMatrix cas2 = codeMatrix code2 := by
  rw [cas2]
  simp only [pcGenerator.eq_def]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul,
    autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [pc2Aut_inv_eq, autMatrix_mul]
  rw [autMatrix_pc1Aut_eq, autMatrix_correctedT_eq,
    autMatrix_swap01Aut_eq, autMatrix_pc3Aut_eq,
    autMatrix_pc2Aut_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cas3_matrix : autMatrix cas3 = codeMatrix code3 := by
  rw [cas3]
  simp only [pcGenerator.eq_def]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [autMatrix_pc4Aut_eq, autMatrix_correctedT_eq,
    autMatrix_swap01Aut_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cas4_matrix : autMatrix cas4 = codeMatrix code4 := by
  rw [cas4]
  simp only [pcGenerator.eq_def]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul,
    autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [autMatrix_correctedT_eq, autMatrix_pc3Aut_eq,
    autMatrix_swap01Aut_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cas5_matrix : autMatrix cas5 = codeMatrix code5 := by
  rw [cas5]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [autMatrix_correctedT_eq, autMatrix_swap01Aut_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pcGenerator_zero_eq_cas_word :
    pcGenerator 0 = cas5 * cas4 * cas2 * cas0 * cas5 := by
  apply autMatrix_injective
  rw [pcGenerator.eq_def, autMatrix_pc1Aut_eq]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [cas5_matrix, cas4_matrix, cas2_matrix, cas0_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pcGenerator_one_eq_cas_word :
    pcGenerator 1 = cas0 * cas1 * cas5 * cas3 * cas4 * cas2 * cas5 * cas4 := by
  apply autMatrix_injective
  rw [pcGenerator.eq_def, autMatrix_pc2Aut_eq]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul,
    autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [cas4_matrix, cas5_matrix, cas2_matrix, cas3_matrix, cas1_matrix,
    cas0_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pcGenerator_two_eq_cas_word :
    pcGenerator 2 = cas0 * cas5 * cas4 * cas0 * cas5 * cas4 * cas2 * cas5 := by
  apply autMatrix_injective
  rw [pcGenerator.eq_def, autMatrix_pc3Aut_eq]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul,
    autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [cas0_matrix, cas5_matrix, cas4_matrix, cas2_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pcGenerator_three_eq_cas_word :
    pcGenerator 3 = cas5 * cas0 * cas1 * cas0 * cas1 * cas5 := by
  apply autMatrix_injective
  rw [pcGenerator.eq_def, autMatrix_pc4Aut_eq]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [cas5_matrix, cas0_matrix, cas1_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pcGenerator_four_eq_cas_word :
    pcGenerator 4 = cas5 * cas0 * cas4 * cas2 * cas5 := by
  apply autMatrix_injective
  rw [pcGenerator.eq_def, autMatrix_pc5Aut_eq]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul]
  rw [cas5_matrix, cas0_matrix, cas4_matrix, cas2_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pcGenerator_five_eq_cas_word :
    pcGenerator 5 = cas5 * cas3 * cas5 := by
  apply autMatrix_injective
  rw [pcGenerator.eq_def, autMatrix_pc6Aut_eq]
  rw [autMatrix_mul, autMatrix_mul]
  rw [cas5_matrix, cas3_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem swap01Aut_eq_cas_word :
    swap01Aut = cas1 * cas5 * cas1 * cas0 * cas3 * cas5 * cas1 := by
  apply autMatrix_injective
  rw [autMatrix_swap01Aut_eq]
  rw [autMatrix_mul, autMatrix_mul, autMatrix_mul, autMatrix_mul,
    autMatrix_mul, autMatrix_mul]
  rw [cas1_matrix, cas5_matrix, cas0_matrix, cas3_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem correctedT_eq_cas_zero : correctedT = cas0 := by
  rfl


end InfoGeometry.Algebra.Zorn.G2CASGeneratorAlignment
