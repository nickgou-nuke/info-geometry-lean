import Mathlib
open Matrix

/-!
# Causal Algebra — 2×2 Operator Algebra for the Proof DAG

Canonical 2×2 matrix realisations of the tri-facet operator O = σ₁,
the forward/backward projectors d/δ, and the Hodge/Dirac Laplacians.

All theorems are proved by direct computation.
-/

namespace InfoGeometry.Causal.Algebra

/-- The Pauli σ₁ matrix — the causal orientation operator. -/
def O : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem O_sq : O * O = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply]

theorem O_cubed : O * O * O = O := by
  rw [O_sq, Matrix.one_mul]

theorem det_O : det O = -1 := by
  unfold O; simp [Matrix.det_fin_two]

theorem tr_O : trace O = 0 := by
  unfold O; simp

/-- Forward projector d = (I + O)/2. -/
noncomputable def d : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 + O)

/-- Backward projector δ = (I - O)/2. -/
noncomputable def δ : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • (1 - O)

/-- Hodge Laplacian Δ_H = dδ + δd. -/
noncomputable def Δ_H : Matrix (Fin 2) (Fin 2) ℂ := d * δ + δ * d

theorem d_mul_δ_zero : d * δ = 0 := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply, Matrix.one_apply]

theorem δ_mul_d_zero : δ * d = 0 := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O, Matrix.mul_apply, Matrix.one_apply]

theorem Δ_H_zero : Δ_H = 0 := by
  unfold Δ_H; rw [d_mul_δ_zero, δ_mul_d_zero, add_zero]

theorem d_add_δ_eq_one : d + δ = 1 := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O] <;> norm_num

theorem d_sub_δ_eq_O : d - δ = O := by
  unfold d δ
  ext i j; fin_cases i <;> fin_cases j <;> simp [O] <;> norm_num

end InfoGeometry.Causal.Algebra
