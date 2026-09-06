import Mathlib
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

open Matrix

section StructureTensor

variable {ι : Type*} [Fintype ι]

def outer2 (u : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => u i * u j

def structureTensor
    (w : ι → ℝ)
    (grad : ι → Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ p, w p • outer2 (grad p)

theorem outer2_transpose (u : Fin 2 → ℝ) :
    (outer2 u)ᵀ = outer2 u := by
  ext i j
  simp [outer2, mul_comm]

theorem structureTensor_symmetric
    (w : ι → ℝ)
    (grad : ι → Fin 2 → ℝ) :
    (structureTensor w grad)ᵀ =
      structureTensor w grad := by
  unfold structureTensor
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.transpose_smul]
  rw [outer2_transpose]

theorem outer2_smul_vector
    (a : ℝ)
    (n : Fin 2 → ℝ) :
    outer2 (fun i => a * n i) =
      a ^ 2 • outer2 n := by
  ext i j
  simp [outer2]
  ring

theorem structureTensor_of_collinear_gradients
    (w : ι → ℝ)
    (grad : ι → Fin 2 → ℝ)
    (n : Fin 2 → ℝ)
    (lam : ι → ℝ)
    (hcol : ∀ p, grad p = fun i => lam p * n i) :
    structureTensor w grad =
      (∑ p, w p * lam p ^ 2) • outer2 n := by
  unfold structureTensor
  simp_rw [hcol, outer2_smul_vector]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_smul]

theorem outer2_det_zero (n : Fin 2 → ℝ) :
    Matrix.det (outer2 n) = 0 := by
  simp [Matrix.det_fin_two, outer2]
  ring

theorem collinear_gradients_det_zero
    (w : ι → ℝ)
    (grad : ι → Fin 2 → ℝ)
    (n : Fin 2 → ℝ)
    (lam : ι → ℝ)
    (hcol : ∀ p, grad p = fun i => lam p * n i) :
    Matrix.det (structureTensor w grad) = 0 := by
  rw [structureTensor_of_collinear_gradients w grad n lam hcol]
  rw [Matrix.det_smul]
  simp [outer2_det_zero]

end StructureTensor
end
