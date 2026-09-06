-/

namespace InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

/-- The Fibonacci fusion matrix `F = [[τ, s], [s, -τ]]`. -/
noncomputable def fibonacciFusionMatrix (τ s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![τ, s; s, -τ]

/-- The diagonal four-anyon `R` matrix with entries `q⁻⁴` and `q³`. -/
noncomputable def fibonacciRMatrix (q : Units ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q ^ (-4 : ℤ) : Units ℂ), 0; 0, (q ^ (3 : ℤ) : Units ℂ)]

/-- The middle-generator matrix obtained by changing to the dual basis and back. -/
noncomputable def fibonacciBMatrix (q : Units ℂ) (τ s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s

/-- Top-left entry of the complex middle-generator matrix `B = F R F`. -/
theorem fibonacciBMatrix_apply_zero_zero (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s 0 0 = τ * τ * q ^ (-4 : ℤ) + s * s * q ^ (3 : ℤ) := by
  simp [fibonacciBMatrix, fibonacciFusionMatrix, fibonacciRMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Top-right entry of the complex middle-generator matrix `B = F R F`. -/
theorem fibonacciBMatrix_apply_zero_one (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s 0 1 = τ * s * q ^ (-4 : ℤ) - τ * s * q ^ (3 : ℤ) := by
  simp [fibonacciBMatrix, fibonacciFusionMatrix, fibonacciRMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring
