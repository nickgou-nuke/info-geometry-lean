import Mathlib

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

end SO55NullSU5KleinSpectral

end noncomputable section
