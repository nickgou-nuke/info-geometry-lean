import InfoGeometry.Algebra.FibonacciParafermion
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The finite graded/off-diagonal readout of the Fibonacci carrier

This owner records only the concrete two-sector grading already present in
`FibonacciParafermion`.  It does not assert a TKK construction or a five
grading: the grading operator is the native `sl₂H` matrix and the odd sector
is represented by the raising/lowering matrices.
-/

namespace FibonacciParafermion

def isOddFor (G X : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  G * X + X * G = 0

def isEvenFor (G X : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  G * X - X * G = 0

/-- The even and odd parts for the involutive `sl₂H` grading. -/
noncomputable def evenPart (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (X + sl₂H * X * sl₂H)

noncomputable def oddPart (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • (X - sl₂H * X * sl₂H)

theorem even_odd_part_sum (X : Matrix (Fin 2) (Fin 2) ℝ) :
    evenPart X + oddPart X = X := by
  dsimp [evenPart, oddPart]
  rw [smul_add, smul_sub]
  module

theorem sl₂H_isEvenFor_sl₂H : isEvenFor sl₂H sl₂H := by
  dsimp [isEvenFor]
  simp

theorem sl₂E_isOddFor_sl₂H : isOddFor sl₂H sl₂E := by
  dsimp [isOddFor]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sl₂H, sl₂E, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl₂F_isOddFor_sl₂H : isOddFor sl₂H sl₂F := by
  dsimp [isOddFor]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sl₂H, sl₂F, Matrix.mul_apply, Fin.sum_univ_two]

theorem majoranaX_isOddFor_sl₂H : isOddFor sl₂H majoranaX := by
  dsimp [isOddFor]
  rw [sl₂H_eq_majoranaZ]
  simpa [add_comm] using majoranaX_majoranaZ_anticomm

theorem sl₂_offDiagonal_readout :
    WeylPlusProjector * sl₂E * WeylMinusProjector = sl₂E ∧
    WeylMinusProjector * sl₂F * WeylPlusProjector = sl₂F ∧
    majoranaX = sl₂E + sl₂F := by
  exact ⟨sl₂E_raises_minus_to_plus, sl₂F_lowers_plus_to_minus,
    majoranaX_is_sl₂_off_diagonal⟩

end FibonacciParafermion
