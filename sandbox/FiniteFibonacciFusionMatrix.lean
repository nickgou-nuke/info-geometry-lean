import Mathlib.Tactic
import InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks
set_option linter.unusedSimpArgs false

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
* the Artin equality is proved by reducing the `2 × 2` matrix identity to
  explicit scalar polynomial identities.

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

lemma q_pow_6 (q : ℂ) (hq5 : q ^ 5 = -1) : q ^ 6 = -q := by
  calc q ^ 6 = q ^ 5 * q := by ring
    _ = -1 * q := by rw [hq5]
    _ = -q := by ring

lemma q_pow_7 (q : ℂ) (hq5 : q ^ 5 = -1) : q ^ 7 = -q ^ 2 := by
  calc q ^ 7 = q ^ 5 * q ^ 2 := by ring
    _ = -1 * q ^ 2 := by rw [hq5]
    _ = -q ^ 2 := by ring

lemma q_pow_8 (q : ℂ) (hq5 : q ^ 5 = -1) : q ^ 8 = -q ^ 3 := by
  calc q ^ 8 = q ^ 5 * q ^ 3 := by ring
    _ = -1 * q ^ 3 := by rw [hq5]
    _ = -q ^ 3 := by ring

lemma q_pow_9 (q : ℂ) (hq5 : q ^ 5 = -1) : q ^ 9 = -q ^ 4 := by
  calc q ^ 9 = q ^ 5 * q ^ 4 := by ring
    _ = -1 * q ^ 4 := by rw [hq5]
    _ = -q ^ 4 := by ring

lemma tau_sq_eq (q τ : ℂ) (hq5 : q ^ 5 = -1) (hτ : τ = q ^ 2 - q ^ 3) :
    τ ^ 2 = q ^ 4 + 2 - q := by
  calc τ ^ 2 = (q ^ 2 - q ^ 3) ^ 2 := by rw [hτ]
    _ = q ^ 4 - 2 * q ^ 5 + q ^ 6 := by ring
    _ = q ^ 4 - 2 * (-1) + (-q) := by rw [hq5, q_pow_6 q hq5]
    _ = q ^ 4 + 2 - q := by ring

/-- Unconditional proof of the Artin relation at the Fibonacci root of unity. -/
theorem fibonacci_fourAnyon_artin
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s := by
  have hR00 : fibonacciRMatrix q 0 0 = -(q : ℂ) := by simp [fibonacciRMatrix]; exact hq_inv
  have hR11 : fibonacciRMatrix q 1 1 = (q : ℂ) ^ 3 := by simp [fibonacciRMatrix]; exact hq_pow3
  have hR01 : fibonacciRMatrix q 0 1 = 0 := by rfl
  have hR10 : fibonacciRMatrix q 1 0 = 0 := by rfl

  have hB00 : fibonacciBMatrix q τ s 0 0 = (q : ℂ) ^ 2 - (q : ℂ) := by
    rw [fibonacciBMatrix_apply_zero_zero]
    rw [hq_inv, hq_pow3]
    calc τ * τ * -(q : ℂ) + s * s * (q : ℂ) ^ 3
      = τ ^ 2 * -(q : ℂ) + s ^ 2 * (q : ℂ) ^ 3 := by ring
      _ = τ ^ 2 * -(q : ℂ) + τ * (q : ℂ) ^ 3 := by rw [hs]
      _ = ((q : ℂ) ^ 4 + 2 - (q : ℂ)) * -(q : ℂ) + ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * (q : ℂ) ^ 3 := by rw [tau_sq_eq (q:ℂ) τ hq5 hτ, hτ]
      _ = -(q : ℂ) ^ 5 - 2 * (q : ℂ) + (q : ℂ) ^ 2 + (q : ℂ) ^ 5 - (q : ℂ) ^ 6 := by ring
      _ = -(-1) - 2 * (q : ℂ) + (q : ℂ) ^ 2 + (-1) - -(q : ℂ) := by rw [hq5, q_pow_6 (q:ℂ) hq5]
      _ = (q : ℂ) ^ 2 - (q : ℂ) := by ring

  have hB01 : fibonacciBMatrix q τ s 0 1 = -s * (q : ℂ) ^ 2 := by
    rw [fibonacciBMatrix_apply_zero_one]
    rw [hq_inv, hq_pow3]
    calc τ * s * -(q : ℂ) - τ * s * (q : ℂ) ^ 3
      = s * (((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * -(q : ℂ) - ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * (q : ℂ) ^ 3) := by rw [hτ]; ring
      _ = s * (-(q : ℂ) ^ 3 + (q : ℂ) ^ 4 - (q : ℂ) ^ 5 + (q : ℂ) ^ 6) := by ring
      _ = s * (-(q : ℂ) ^ 3 + (q : ℂ) ^ 4 - (-1) + -(q : ℂ)) := by rw [hq5, q_pow_6 (q:ℂ) hq5]
      _ = s * ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) + 1) := by ring
      _ = s * (-(q : ℂ) ^ 2) := by
        have h_sub : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) + 1 = -(q : ℂ) ^ 2 := by
          calc (q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) + 1 = ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1) - (q : ℂ) ^ 2 := by ring
            _ = 0 - (q : ℂ) ^ 2 := by rw [h_poly]
            _ = -(q : ℂ) ^ 2 := by ring
        rw [h_sub]
      _ = -s * (q : ℂ) ^ 2 := by ring

  have hB10 : fibonacciBMatrix q τ s 1 0 = -s * (q : ℂ) ^ 2 := by
    rw [fibonacciBMatrix_apply_one_zero]
    rw [hq_inv, hq_pow3]
    calc τ * s * -(q : ℂ) - τ * s * (q : ℂ) ^ 3
      = s * (((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * -(q : ℂ) - ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * (q : ℂ) ^ 3) := by rw [hτ]; ring
      _ = s * (-(q : ℂ) ^ 3 + (q : ℂ) ^ 4 - (q : ℂ) ^ 5 + (q : ℂ) ^ 6) := by ring
      _ = s * (-(q : ℂ) ^ 3 + (q : ℂ) ^ 4 - (-1) + -(q : ℂ)) := by rw [hq5, q_pow_6 (q:ℂ) hq5]
      _ = s * ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) + 1) := by ring
      _ = s * (-(q : ℂ) ^ 2) := by
        have h_sub : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) + 1 = -(q : ℂ) ^ 2 := by
          calc (q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) + 1 = ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1) - (q : ℂ) ^ 2 := by ring
            _ = 0 - (q : ℂ) ^ 2 := by rw [h_poly]
            _ = -(q : ℂ) ^ 2 := by ring
        rw [h_sub]
      _ = -s * (q : ℂ) ^ 2 := by ring

  have hB11 : fibonacciBMatrix q τ s 1 1 = -(q : ℂ) ^ 2 + (q : ℂ) ^ 3 := by
    rw [fibonacciBMatrix_apply_one_one]
    rw [hq_inv, hq_pow3]
    calc s * s * -(q : ℂ) + τ * τ * (q : ℂ) ^ 3
      = s ^ 2 * -(q : ℂ) + τ ^ 2 * (q : ℂ) ^ 3 := by ring
      _ = τ * -(q : ℂ) + τ ^ 2 * (q : ℂ) ^ 3 := by rw [hs]
      _ = ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * -(q : ℂ) + ((q : ℂ) ^ 4 + 2 - (q : ℂ)) * (q : ℂ) ^ 3 := by rw [tau_sq_eq (q:ℂ) τ hq5 hτ, hτ]
      _ = -(q : ℂ) ^ 3 + (q : ℂ) ^ 4 + (q : ℂ) ^ 7 + 2 * (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by ring
      _ = -(q : ℂ) ^ 3 + (q : ℂ) ^ 4 + -(q : ℂ) ^ 2 + 2 * (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by rw [q_pow_7 (q:ℂ) hq5]
      _ = -(q : ℂ) ^ 2 + (q : ℂ) ^ 3 := by ring

  have hLHS00 : (fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q) 0 0 = (q : ℂ) ^ 4 - (q : ℂ) ^ 3 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    ring
  have hLHS01 : (fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q) 0 1 = -s * (q : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc -(q : ℂ) * (-s * (q : ℂ) ^ 2) * (q : ℂ) ^ 3
      = s * (q : ℂ) ^ 6 := by ring
      _ = s * -(q : ℂ) := by rw [q_pow_6 (q:ℂ) hq5]
      _ = -s * (q : ℂ) := by ring
  have hLHS10 : (fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q) 1 0 = -s * (q : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc (q : ℂ) ^ 3 * (-s * (q : ℂ) ^ 2) * -(q : ℂ)
      = s * (q : ℂ) ^ 6 := by ring
      _ = s * -(q : ℂ) := by rw [q_pow_6 (q:ℂ) hq5]
      _ = -s * (q : ℂ) := by ring
  have hLHS11 : (fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q) 1 1 = (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc (q : ℂ) ^ 3 * (-(q : ℂ) ^ 2 + (q : ℂ) ^ 3) * (q : ℂ) ^ 3
      = -(q : ℂ) ^ 8 + (q : ℂ) ^ 9 := by ring
      _ = -(q : ℂ) ^ 5 * (q : ℂ) ^ 3 + (q : ℂ) ^ 5 * (q : ℂ) ^ 4 := by ring
      _ = -(-1) * (q : ℂ) ^ 3 + (-1) * (q : ℂ) ^ 4 := by rw [hq5]
      _ = (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by ring

  have hRHS00 : (fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) 0 0 = (q : ℂ) ^ 4 - (q : ℂ) ^ 3 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc ((q : ℂ) ^ 2 - (q : ℂ)) * -(q : ℂ) * ((q : ℂ) ^ 2 - (q : ℂ)) + (-s * (q : ℂ) ^ 2) * (q : ℂ) ^ 3 * (-s * (q : ℂ) ^ 2)
      = -(q : ℂ) * ((q : ℂ) ^ 2 - (q : ℂ)) ^ 2 + s ^ 2 * (q : ℂ) ^ 7 := by ring
      _ = -(q : ℂ) * ((q : ℂ) ^ 2 - (q : ℂ)) ^ 2 + τ * -(q : ℂ) ^ 2 := by rw [hs, q_pow_7 (q:ℂ) hq5]
      _ = -(q : ℂ) * ((q : ℂ) ^ 2 - (q : ℂ)) ^ 2 + ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) * -(q : ℂ) ^ 2 := by rw [hτ]
      _ = -(q : ℂ) ^ 5 + 2 * (q : ℂ) ^ 4 - (q : ℂ) ^ 3 - (q : ℂ) ^ 4 + (q : ℂ) ^ 5 := by ring
      _ = (q : ℂ) ^ 4 - (q : ℂ) ^ 3 := by ring

  have hRHS01 : (fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) 0 1 = -s * (q : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc ((q : ℂ) ^ 2 - (q : ℂ)) * -(q : ℂ) * (-s * (q : ℂ) ^ 2) + (-s * (q : ℂ) ^ 2) * (q : ℂ) ^ 3 * (-(q : ℂ) ^ 2 + (q : ℂ) ^ 3)
      = s * (q : ℂ) ^ 5 - s * (q : ℂ) ^ 4 + s * (q : ℂ) ^ 7 - s * (q : ℂ) ^ 8 := by ring
      _ = s * (-1) - s * (q : ℂ) ^ 4 + s * -(q : ℂ) ^ 2 - s * -(q : ℂ) ^ 3 := by rw [hq5, q_pow_7 (q:ℂ) hq5, q_pow_8 (q:ℂ) hq5]
      _ = -s - s * (q : ℂ) ^ 4 - s * (q : ℂ) ^ 2 + s * (q : ℂ) ^ 3 := by ring
      _ = -s * ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 + 1) := by ring
      _ = -s * ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 + (q : ℂ)) := by ring
      _ = -s * (0 + (q : ℂ)) := by rw [h_poly]
      _ = -s * (q : ℂ) := by ring

  have hRHS10 : (fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) 1 0 = -s * (q : ℂ) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc (-s * (q : ℂ) ^ 2) * -(q : ℂ) * ((q : ℂ) ^ 2 - (q : ℂ)) + (-(q : ℂ) ^ 2 + (q : ℂ) ^ 3) * (q : ℂ) ^ 3 * (-s * (q : ℂ) ^ 2)
      = s * (q : ℂ) ^ 5 - s * (q : ℂ) ^ 4 + s * (q : ℂ) ^ 7 - s * (q : ℂ) ^ 8 := by ring
      _ = s * (-1) - s * (q : ℂ) ^ 4 + s * -(q : ℂ) ^ 2 - s * -(q : ℂ) ^ 3 := by rw [hq5, q_pow_7 (q:ℂ) hq5, q_pow_8 (q:ℂ) hq5]
      _ = -s - s * (q : ℂ) ^ 4 - s * (q : ℂ) ^ 2 + s * (q : ℂ) ^ 3 := by ring
      _ = -s * ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 + 1) := by ring
      _ = -s * ((q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 + (q : ℂ)) := by ring
      _ = -s * (0 + (q : ℂ)) := by rw [h_poly]
      _ = -s * (q : ℂ) := by ring

  have hRHS11 : (fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) 1 1 = (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hR00, hR11, hR01, hR10, hB00, hB01, hB10, hB11, mul_zero, zero_mul, add_zero, zero_add]
    calc (-s * (q : ℂ) ^ 2) * -(q : ℂ) * (-s * (q : ℂ) ^ 2) + (-(q : ℂ) ^ 2 + (q : ℂ) ^ 3) * (q : ℂ) ^ 3 * (-(q : ℂ) ^ 2 + (q : ℂ) ^ 3)
      = -s ^ 2 * (q : ℂ) ^ 5 + (q : ℂ) ^ 7 - 2 * (q : ℂ) ^ 8 + (q : ℂ) ^ 9 := by ring
      _ = -τ * (-1) + -(q : ℂ) ^ 2 - 2 * -(q : ℂ) ^ 3 + -(q : ℂ) ^ 4 := by rw [hs, hq5, q_pow_7 (q:ℂ) hq5, q_pow_8 (q:ℂ) hq5, q_pow_9 (q:ℂ) hq5]
      _ = τ - (q : ℂ) ^ 2 + 2 * (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by ring
      _ = ((q : ℂ) ^ 2 - (q : ℂ) ^ 3) - (q : ℂ) ^ 2 + 2 * (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by rw [hτ]
      _ = (q : ℂ) ^ 3 - (q : ℂ) ^ 4 := by ring

  ext i j
  fin_cases i <;> fin_cases j
  · exact Eq.trans hLHS00 hRHS00.symm
  · exact Eq.trans hLHS01 hRHS01.symm
  · exact Eq.trans hLHS10 hRHS10.symm
  · exact Eq.trans hLHS11 hRHS11.symm

end InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
