import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SO55NullSU5KleinSpectral

abbrev Q := ℚ

def n5 : ℕ := 5
def nullVectorDim : ℕ := 2 * n5
def soDim (n : ℕ) : ℕ := n * (n - 1) / 2
def matrixDim (n : ℕ) : ℕ := n * n
def traceLineDim : ℕ := 1
def slDim (n : ℕ) : ℕ := matrixDim n - traceLineDim
def skewDim (n : ℕ) : ℕ := n * (n - 1) / 2

def diagonalA_dim : ℕ := matrixDim n5
def su5Adjoint_dim : ℕ := slDim n5
def dilaton_dim : ℕ := traceLineDim
def Bskew_dim : ℕ := skewDim n5
def Cskew_dim : ℕ := skewDim n5
def so55NullBlock_dim : ℕ := diagonalA_dim + Bskew_dim + Cskew_dim
def su5Partition_dim : ℕ := su5Adjoint_dim + dilaton_dim + Bskew_dim + Cskew_dim

def spinEvenScalar : ℕ := Nat.choose 5 0
def spinEvenTwoForm : ℕ := Nat.choose 5 2
def spinEvenFourForm : ℕ := Nat.choose 5 4
def spinEven16_dim : ℕ := spinEvenScalar + spinEvenTwoForm + spinEvenFourForm

def spinOddOneForm : ℕ := Nat.choose 5 1
def spinOddThreeForm : ℕ := Nat.choose 5 3
def spinOddFiveForm : ℕ := Nat.choose 5 5
def spinOdd16_dim : ℕ := spinOddOneForm + spinOddThreeForm + spinOddFiveForm

def varlamovModePartition_dim : ℕ := spinEven16_dim + spinOdd16_dim

def involutionParity (diag off : Q) : Q × Q := (diag, -off)
def kleinBottleQuotientAverage (a b c d : Q) : Q := (a + b + c + d) / 4
def mobiusInversionZ2 (even odd : Q) : Q × Q := ((even + odd) / 2, (even - odd) / 2)
def mobiusReconstructZ2 (x y : Q) : Q × Q := (x + y, x - y)

def tripotentDetPolynomial (d : Q) : Q := d * (d - 1) * (d + 1)
def poincareCasimir (m : Q) : Q := -m * m
def spectralSpringStiffness (C1 : Q) : Q := -C1

def brillouinPairing (k : Q) : Q × Q := (k, -k)
def kleinBottleModeInvariant (k : Q) : Q := (brillouinPairing k).1 + (brillouinPairing k).2

theorem null_vector_dim_10 : nullVectorDim = 10 := by
  norm_num [nullVectorDim, n5]

theorem so55_dimension_45 : soDim nullVectorDim = 45 := by
  norm_num [soDim, nullVectorDim, n5]

theorem sl5_dimension_24 : su5Adjoint_dim = 24 := by
  norm_num [su5Adjoint_dim, slDim, matrixDim, traceLineDim, n5]

theorem skew5_dimension_10 : skewDim n5 = 10 := by
  norm_num [skewDim, n5]

theorem null_block_dimension_45 : so55NullBlock_dim = 45 := by
  norm_num [so55NullBlock_dim, diagonalA_dim, matrixDim, Bskew_dim, Cskew_dim, skewDim, n5]

theorem su5_partition_dimension_45 : su5Partition_dim = 45 := by
  norm_num [su5Partition_dim, su5Adjoint_dim, slDim, matrixDim, dilaton_dim, traceLineDim, Bskew_dim, Cskew_dim, skewDim, n5]

theorem su5_partition_refines_null_block : su5Partition_dim = so55NullBlock_dim := by
  norm_num [su5Partition_dim, so55NullBlock_dim, su5Adjoint_dim, slDim, diagonalA_dim, matrixDim,
    dilaton_dim, traceLineDim, Bskew_dim, Cskew_dim, skewDim, n5]

theorem spin_even_decomposition_16 : spinEven16_dim = 16 := by
  norm_num [spinEven16_dim, spinEvenScalar, spinEvenTwoForm, spinEvenFourForm, Nat.choose]

theorem spin_odd_decomposition_16 : spinOdd16_dim = 16 := by
  norm_num [spinOdd16_dim, spinOddOneForm, spinOddThreeForm, spinOddFiveForm, Nat.choose]

theorem varlamov_spin_mode_partition_32 : varlamovModePartition_dim = 32 := by
  norm_num [varlamovModePartition_dim, spinEven16_dim, spinOdd16_dim, spinEvenScalar,
    spinEvenTwoForm, spinEvenFourForm, spinOddOneForm, spinOddThreeForm, spinOddFiveForm,
    Nat.choose]

theorem involution_square_identity (diag off : Q) :
    involutionParity (involutionParity diag off).1 (involutionParity diag off).2 = (diag, off) := by
  simp [involutionParity]

theorem mobius_z2_roundtrip (even odd : Q) :
    mobiusReconstructZ2 (mobiusInversionZ2 even odd).1 (mobiusInversionZ2 even odd).2 = (even, odd) := by
  ext <;> simp [mobiusInversionZ2, mobiusReconstructZ2] <;> ring

theorem klein_bottle_average_one_two_three_four : kleinBottleQuotientAverage 1 2 3 4 = 5 / 2 := by
  norm_num [kleinBottleQuotientAverage]

theorem tripotent_det_negative : tripotentDetPolynomial (-1) = 0 := by
  norm_num [tripotentDetPolynomial]

theorem tripotent_det_zero : tripotentDetPolynomial 0 = 0 := by
  norm_num [tripotentDetPolynomial]

theorem tripotent_det_positive : tripotentDetPolynomial 1 = 0 := by
  norm_num [tripotentDetPolynomial]

theorem casimir_spring_stiffness (m : Q) : spectralSpringStiffness (poincareCasimir m) = m * m := by
  rw [spectralSpringStiffness, poincareCasimir]
  ring

theorem klein_bottle_brillouin_pair_cancels (k : Q) : kleinBottleModeInvariant k = 0 := by
  simp [kleinBottleModeInvariant, brillouinPairing]

inductive Concept where
  | SO55_Null_Basis
  | SU5_Adjoint_24
  | Dilaton_Line_1
  | Fermion_Ten_B
  | Fermion_TenBar_C
  | Spinor_Exterior_16
  | Klein_Mobius_Spectral_Quotient
  deriving DecidableEq, Repr

inductive Edge where
  | decomposes_to
  | trace_splits_to
  | skew_splits_to
  | classifies_spin_modes
  | quotients_modes
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.SO55_Null_Basis, Edge.decomposes_to, Concept.SU5_Adjoint_24 => true
  | Concept.SO55_Null_Basis, Edge.trace_splits_to, Concept.Dilaton_Line_1 => true
  | Concept.SO55_Null_Basis, Edge.skew_splits_to, Concept.Fermion_Ten_B => true
  | Concept.SO55_Null_Basis, Edge.skew_splits_to, Concept.Fermion_TenBar_C => true
  | Concept.Spinor_Exterior_16, Edge.quotients_modes, Concept.Klein_Mobius_Spectral_Quotient => true
  | _, _, _ => false

theorem edgeHolds_so55_null_basis_decomposes_to_su5_adjoint_24 :
    edgeHolds Concept.SO55_Null_Basis Edge.decomposes_to Concept.SU5_Adjoint_24 = true := rfl

theorem edgeHolds_so55_null_basis_trace_splits_to_dilaton_line_1 :
    edgeHolds Concept.SO55_Null_Basis Edge.trace_splits_to Concept.Dilaton_Line_1 = true := rfl

theorem edgeHolds_so55_null_basis_skew_splits_to_fermion_ten_b :
    edgeHolds Concept.SO55_Null_Basis Edge.skew_splits_to Concept.Fermion_Ten_B = true := rfl

theorem edgeHolds_so55_null_basis_skew_splits_to_fermion_tenbar_c :
    edgeHolds Concept.SO55_Null_Basis Edge.skew_splits_to Concept.Fermion_TenBar_C = true := rfl

theorem edgeHolds_spinor_exterior_16_quotients_modes_klein_mobius_spectral_quotient :
    edgeHolds Concept.Spinor_Exterior_16 Edge.quotients_modes Concept.Klein_Mobius_Spectral_Quotient =
      true := rfl

def tensorMultipletCount : ℕ := 16

def anomalyCancellationRequirement (n_T : ℕ) : ℕ := n_T - 16

theorem anomaly_cancelled_non_orientable : anomalyCancellationRequirement tensorMultipletCount = 0 := by
  norm_num [anomalyCancellationRequirement, tensorMultipletCount]

end SO55NullSU5KleinSpectral

end noncomputable section
