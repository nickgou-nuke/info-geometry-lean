import Mathlib.Tactic
open Matrix

set_option autoImplicit false

/-!
# Verlinde S-Matrix for the Fibonacci Anyon Model

The Verlinde S-matrix encodes the modular transformation `τ ↦ -1/τ` of the
characters in a rational CFT.  For the Fibonacci anyon model (rank 2, quantum
dimension `φ = (1+√5)/2`), the S-matrix is real and symmetric:

```
S = [[1/φ,  1/√φ ],
     [1/√φ, -1/φ ]]
```

Key properties:
- **Involutive**: `S² = I`.
- **det(S) = -1**, **tr(S) = 0**.
- **Fibonacci identity**: `φ² = φ + 1`.

All theorems are proven by direct 2×2 computation over ℝ.
-/

namespace Audit.VerlindeSMatrix

section GoldenRatio

/-- The golden ratio φ = (1+√5)/2, as a real number. -/
noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem φ_sq_eq_φ_add_one : φ ^ 2 = φ + 1 := by
  unfold φ
  have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

theorem φ_pos : 0 < φ := by
  unfold φ
  have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  nlinarith

theorem φ_ne_zero : φ ≠ 0 := by exact ne_of_gt φ_pos

theorem sqrt_φ_sq : (Real.sqrt φ) ^ 2 = φ :=
  Real.sq_sqrt (by linarith [φ_pos])

theorem sqrt_φ_pos : 0 < Real.sqrt φ :=
  Real.sqrt_pos.mpr φ_pos

theorem sqrt_φ_ne_zero : Real.sqrt φ ≠ 0 := by
  exact ne_of_gt sqrt_φ_pos

end GoldenRatio

section VerlindeS

/-- Verlinde S-matrix for the Fibonacci model (real entries). -/
noncomputable def S : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 / φ), (1 / Real.sqrt φ); (1 / Real.sqrt φ), -(1 / φ)]

theorem S_sq_eq_one : S * S = 1 := by
  ext i j; fin_cases i <;> fin_cases j
  · -- (0,0): (1/φ)² + (1/√φ)² = 1
    simp [S, Matrix.mul_apply]
    field_simp [φ_ne_zero, sqrt_φ_ne_zero]
    rw [sqrt_φ_sq]
    nlinarith [φ_sq_eq_φ_add_one]
  · -- (0,1): (1/φ)(1/√φ) + (1/√φ)(-1/φ) = 0
    simp [S, Matrix.mul_apply]
    ring
  · -- (1,0): symmetric
    simp [S, Matrix.mul_apply]
    ring
  · -- (1,1): (1/√φ)² + (1/φ)² = 1
    simp [S, Matrix.mul_apply]
    field_simp [φ_ne_zero, sqrt_φ_ne_zero]
    rw [sqrt_φ_sq]
    nlinarith [φ_sq_eq_φ_add_one]

theorem det_S : det S = -1 := by
  unfold S
  simp [Matrix.det_fin_two]
  field_simp [φ_ne_zero, sqrt_φ_ne_zero]
  rw [sqrt_φ_sq]
  nlinarith [φ_sq_eq_φ_add_one]

theorem tr_S : trace S = 0 := by
  unfold S; simp

/-- S is involutive with det = -1, tr = 0. -/
theorem eigenvalues_plus_minus_one : S * S = 1 ∧ det S = -1 ∧ trace S = 0 := by
  exact ⟨S_sq_eq_one, det_S, tr_S⟩

end VerlindeS

end Audit.VerlindeSMatrix
