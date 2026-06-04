import Mathlib
open Matrix

set_option autoImplicit false

/-!
# Hodge d/δ/Δ Operator Realization

The tri-facet operator `O = σ₁ = [[0,1],[1,0]]` (with `O³ = O`) gives a
concrete 2×2 matrix realisation of the Hodge–Krein decomposition:

- **d** = `P_ext = (1/2)(O² + O) = (1/2)(I + O)` — projector onto `+1`.
- **δ** = `P_coext = (1/2)(O² - O) = (1/2)(I - O)` — projector onto `-1`.
- **d + δ = I**, **d - δ = O**.
- **Δ_H** = `dδ + δd = 0` — Hodge Laplacian (vanishes).
- **D** = `d + δ = I` — Dirac operator.
- **Δ_D** = `D² = I` — Dirac Laplacian.

All theorems are proven by direct 2×2 matrix computation over ℂ.
-/

namespace Audit.HodgeDiracDelta

section Operators

/-- Pauli σ₁ = [[0,1],[1,0]] — the tri-facet operator satisfying O³ = O. -/
def O : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem O_sq : O * O = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply]

theorem O_cubed : O * O * O = O := by
  rw [O_sq, Matrix.one_mul]

/-- Exterior derivative d = (I + O)/2. -/
noncomputable def d : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 + O)

/-- Codifferential δ = (I - O)/2. -/
noncomputable def δ : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 - O)

/-- Hodge Laplacian Δ_H = dδ + δd = 0. -/
noncomputable def Δ_H : Matrix (Fin 2) (Fin 2) ℂ := d * δ + δ * d

/-- Dirac operator D = d + δ = I. -/
noncomputable def D : Matrix (Fin 2) (Fin 2) ℂ := d + δ

/-- Dirac Laplacian Δ_D = D² = I. -/
noncomputable def Δ_D : Matrix (Fin 2) (Fin 2) ℂ := D * D

theorem d_mul_δ : d * δ = 0 := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply, Matrix.one_apply]

theorem δ_mul_d : δ * d = 0 := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply, Matrix.one_apply]

theorem Δ_H_zero : Δ_H = 0 := by
  unfold Δ_H; rw [d_mul_δ, δ_mul_d, add_zero]

theorem d_add_δ_eq_one : D = 1 := by
  unfold D d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O] <;> ring

theorem Δ_D_eq_one : Δ_D = 1 := by
  unfold Δ_D; rw [d_add_δ_eq_one, Matrix.one_mul]

theorem d_sub_δ_eq_O : d - δ = O := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O] <;> ring

theorem det_O : det O = -1 := by
  unfold O; simp [Matrix.det_fin_two]

theorem tr_O : trace O = 0 := by
  unfold O; simp

end Operators

section Harmonic

/--
The Hodge Laplacian Δ_H = 0, so every vector is Δ_H-harmonic.
-/
theorem ker_Δ_H_is_whole_space (x : Matrix (Fin 2) (Fin 1) ℂ) : Δ_H * x = 0 := by
  rw [Δ_H_zero, Matrix.zero_mul]

/--
The Dirac operator D = I is invertible, so ker(Δ_D) = {0}.
-/
theorem ker_Δ_D_trivial (x : Matrix (Fin 2) (Fin 1) ℂ) (hx : D * x = 0) : x = 0 := by
  have hD : D = 1 := d_add_δ_eq_one
  rw [hD, Matrix.one_mul] at hx
  exact hx

end Harmonic

end Audit.HodgeDiracDelta
