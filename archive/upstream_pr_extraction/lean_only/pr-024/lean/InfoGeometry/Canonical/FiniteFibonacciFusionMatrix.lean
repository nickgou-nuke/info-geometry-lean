import Mathlib.Tactic
import InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

/-!
# InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

Finite algebraic fusion-matrix interface for the four-Fibonacci-anyon sector.

The analytic paper obtains a dual basis `Θ` and a fusion matrix

```text
F = [[τ, √τ], [√τ, -τ]]
```

with `τ² + τ = 1`.  This file formalizes the finite algebraic content of that
basis change:

* the `2 × 2` fusion matrix over `ℂ`, parameterized by `τ` and a square-root
  parameter `s` with `s² = τ`;
* `F² = 1` from the two explicit scalar hypotheses;
* `det F = -1`;
* the middle braid readout is the conjugate `B = F R F`;
* the Artin equality is exposed only as an explicit finite matrix hypothesis,
  not as an analytic-continuation theorem.

No hypergeometric functions.
No gamma-function identities.
No analytic continuation.
No proof that a concrete complex root `q = exp(iπ/5)` satisfies the braid relation.
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

/-- Bottom-left entry of the complex middle-generator matrix `B = F R F`. -/
theorem fibonacciBMatrix_apply_one_zero (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s 1 0 = τ * s * q ^ (-4 : ℤ) - τ * s * q ^ (3 : ℤ) := by
  simp [fibonacciBMatrix, fibonacciFusionMatrix, fibonacciRMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Bottom-right entry of the complex middle-generator matrix `B = F R F`. -/
theorem fibonacciBMatrix_apply_one_one (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s 1 1 = s * s * q ^ (-4 : ℤ) + τ * τ * q ^ (3 : ℤ) := by
  simp [fibonacciBMatrix, fibonacciFusionMatrix, fibonacciRMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The complex middle-generator matrix `B = F R F` is symmetric. -/
theorem fibonacciBMatrix_symmetric (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s 0 1 = fibonacciBMatrix q τ s 1 0 := by
  rw [fibonacciBMatrix_apply_zero_one, fibonacciBMatrix_apply_one_zero]

/-- The fusion matrix is involutive when `s² = τ` and `τ² + τ = 1`. -/
theorem fibonacciFusionMatrix_sq
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fibonacciFusionMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [← hτ, ← hs]
    ring
  · ring
  · ring
  · rw [← hτ, ← hs]
    ring

/-- The fusion matrix has determinant `-1` under the same finite hypotheses. -/
theorem det_fibonacciFusionMatrix
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (fibonacciFusionMatrix τ s).det = -1 := by
  simp [fibonacciFusionMatrix, Matrix.det_fin_two]
  rw [← hτ, ← hs]
  ring

/-- The dual-basis change is its own inverse. -/
theorem fibonacciFusionMatrix_inv_eq_self
    {τ s : ℂ} (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 :=
  fibonacciFusionMatrix_sq hs hτ

/--
Finite Artin check for the four-anyon matrices, kept theorem-owned by requiring
the exact matrix equality as an explicit algebraic hypothesis.
-/
theorem fibonacci_fourAnyon_artin_from_matrix_identity
    (q : Units ℂ) (τ s : ℂ)
    (hArtin : fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) :
    fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s :=
  hArtin

end InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
