import Mathlib.Tactic

noncomputable section

namespace SarsSKMajoranaSYK

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

open scoped Matrix

def dlaDimSYK (n : ℕ) : ℕ :=
  2^(2 * n - 1) - 2

def dlaDimSK (L : ℕ) : ℕ :=
  2 * (4^(L - 1) - 1)

def poolSizeSK (L : ℕ) : ℕ :=
  L * (L - 1)

def poolSizeSYK (n : ℕ) : ℕ :=
  n + 3 * n * (n - 1) / 2

def majoranaCount (n : ℕ) : ℕ :=
  2 * n

def hilbertDim (n : ℕ) : ℕ :=
  2^n

def matrixAlgDim (n : ℕ) : ℕ :=
  (hilbertDim n)^2

def cliffordRealBalancedDim (n : ℕ) : ℕ :=
  2^(2*n)

def cl55MatrixSide : ℕ := 32

def cl55MatrixDim : ℕ := cl55MatrixSide^2

structure SYKMajoranaSystem where
  n : ℕ

namespace SYKMajoranaSystem

def N (S : SYKMajoranaSystem) : ℕ := majoranaCount S.n

@[simp] theorem N_eq (S : SYKMajoranaSystem) :
    S.N = majoranaCount S.n := rfl

def dla_dim (S : SYKMajoranaSystem) : ℕ := dlaDimSYK S.n

def pool_size (S : SYKMajoranaSystem) : ℕ := poolSizeSYK S.n

end SYKMajoranaSystem

structure SKSpinChain where
  L : ℕ

namespace SKSpinChain

def dla_dim (S : SKSpinChain) : ℕ := dlaDimSK S.L

def pool_size (S : SKSpinChain) : ℕ := poolSizeSK S.L

end SKSpinChain

structure PauliPairPool where
  L : ℕ

namespace PauliPairPool

def zy_terms (P : PauliPairPool) : ℕ := P.L * (P.L - 1) / 2

def yz_terms (P : PauliPairPool) : ℕ := P.L * (P.L - 1) / 2

end PauliPairPool

def pauliPoolTotal (P : PauliPairPool) : ℕ :=
  P.zy_terms + P.yz_terms

def I2 : M2C := !![1, 0; 0, 1]
def X : M2C := !![0, 1; 1, 0]
def Y : M2C := !![0, -Complex.I; Complex.I, 0]
def Z : M2C := !![1, 0; 0, -1]

def antiComm (A B : M2C) : M2C := A * B + B * A

theorem pauli_X_square : X * X = I2 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [X, I2, Matrix.mul_apply]

theorem pauli_Y_square : Y * Y = I2 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Y, I2, Matrix.mul_apply, Complex.I_mul_I]

theorem pauli_Z_square : Z * Z = I2 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [Z, I2, Matrix.mul_apply]

theorem pauli_XY_anticomm : antiComm X Y = 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [antiComm, X, Y]

theorem pauli_XZ_anticomm : antiComm X Z = 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [antiComm, X, Z, Matrix.mul_apply]

theorem pauli_YZ_anticomm : antiComm Y Z = 0 := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [antiComm, Y, Z]

theorem dla_dim_syk_n4 : dlaDimSYK 4 = 126 := by
  norm_num [dlaDimSYK]

theorem dla_dim_sk_L8 : dlaDimSK 8 = 32766 := by
  norm_num [dlaDimSK]

theorem pool_sk_L8 : poolSizeSK 8 = 56 := by
  norm_num [poolSizeSK]

theorem pool_syk_n4 : poolSizeSYK 4 = 22 := by
  norm_num [poolSizeSYK]

theorem majorana_N8_n4 : majoranaCount 4 = 8 := by
  norm_num [majoranaCount]

theorem hilbert_dim_n10 : hilbertDim 10 = 1024 := by
  norm_num [hilbertDim]

theorem cl55_matrix_dim_eq_clifford_dim : cl55MatrixDim = 2^10 := by
  norm_num [cl55MatrixDim, cl55MatrixSide]

theorem balanced_clifford_dim_n5 : cliffordRealBalancedDim 5 = 1024 := by
  norm_num [cliffordRealBalancedDim]

theorem matrix_alg_dim_n5 : matrixAlgDim 5 = 1024 := by
  norm_num [matrixAlgDim, hilbertDim]

theorem sk_syk_dim_comparison : dlaDimSYK 4 < dlaDimSK 8 := by
  norm_num [dlaDimSYK, dlaDimSK]

inductive Concept where
  | Quantum_SK_Model
  | SYK_Majorana_Model
  | Symmetry_Adapted_Operator_Pool
  | Jordan_Wigner_Clifford_Embedding
  | Pin55_Spinor_Block
  | Dense_Dynamical_Lie_Algebra
  deriving DecidableEq, Repr

inductive Edge where
  | has_pool_size
  | has_dla_dimension
  | embeds_by
  | realizes_cl55_block
  | scales_as
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Quantum_SK_Model, Edge.has_pool_size, Concept.Symmetry_Adapted_Operator_Pool => true
  | Concept.SYK_Majorana_Model, Edge.has_pool_size, Concept.Symmetry_Adapted_Operator_Pool => true
  | Concept.SYK_Majorana_Model, Edge.embeds_by, Concept.Jordan_Wigner_Clifford_Embedding => true
  | Concept.Jordan_Wigner_Clifford_Embedding, Edge.realizes_cl55_block, Concept.Pin55_Spinor_Block => true
  | Concept.SYK_Majorana_Model, Edge.has_dla_dimension, Concept.Dense_Dynamical_Lie_Algebra => true
  | Concept.Dense_Dynamical_Lie_Algebra, Edge.scales_as, Concept.SYK_Majorana_Model => true
  | _, _, _ => false

theorem quantum_sk_has_pool_size_edge :
    edgeHolds Concept.Quantum_SK_Model Edge.has_pool_size Concept.Symmetry_Adapted_Operator_Pool = true := by
  rfl

theorem syk_has_pool_size_edge :
    edgeHolds Concept.SYK_Majorana_Model Edge.has_pool_size Concept.Symmetry_Adapted_Operator_Pool = true := by
  rfl

theorem syk_embeds_by_jordan_wigner_edge :
    edgeHolds Concept.SYK_Majorana_Model Edge.embeds_by Concept.Jordan_Wigner_Clifford_Embedding = true := by
  rfl

theorem jordan_wigner_realizes_cl55_block_edge :
    edgeHolds Concept.Jordan_Wigner_Clifford_Embedding Edge.realizes_cl55_block Concept.Pin55_Spinor_Block = true := by
  rfl

theorem syk_has_dla_dimension_edge :
    edgeHolds Concept.SYK_Majorana_Model Edge.has_dla_dimension Concept.Dense_Dynamical_Lie_Algebra = true := by
  rfl

theorem dla_scales_as_syk_edge :
    edgeHolds Concept.Dense_Dynamical_Lie_Algebra Edge.scales_as Concept.SYK_Majorana_Model = true := by
  rfl

end SarsSKMajoranaSYK

end noncomputable section
