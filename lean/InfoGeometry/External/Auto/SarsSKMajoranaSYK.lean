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

end SarsSKMajoranaSYK

end noncomputable section
