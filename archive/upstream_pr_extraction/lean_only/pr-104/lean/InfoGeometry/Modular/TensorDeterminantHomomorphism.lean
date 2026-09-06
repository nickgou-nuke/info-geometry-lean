import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Modular.Tensor

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

local notation "dimM" => Fintype.card m
local notation "dimN" => Fintype.card n

def tensorProd (A : Matrix m m R) (B : Matrix n n R) : Matrix (m × n) (m × n) R :=
  fun ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ => A i₁ i₂ * B j₁ j₂

theorem tensorProd_mul (A₁ A₂ : Matrix m m R) (B₁ B₂ : Matrix n n R) :
    tensorProd (A₁ * A₂) (B₁ * B₂) = tensorProd A₁ B₁ * tensorProd A₂ B₂ := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [tensorProd, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  have h_sum : (∑ i : m, ∑ j : n, (A₁ i₁ i * B₁ j₁ j) * (A₂ i i₂ * B₂ j j₂)) =
      (∑ i : m, A₁ i₁ i * A₂ i i₂) * (∑ j : n, B₁ j₁ j * B₂ j j₂) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  exact h_sum.symm

@[simp]
theorem tensorProd_one :
    tensorProd (1 : Matrix m m R) (1 : Matrix n n R) = 1 := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [tensorProd, Matrix.one_apply]
  by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]

theorem tensorProd_trace (A : Matrix m m R) (B : Matrix n n R) :
    Matrix.trace (tensorProd A B) = Matrix.trace A * Matrix.trace B := by
  dsimp [tensorProd, Matrix.trace]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

def diagMat (u : m → R) : Matrix m m R :=
  fun i j => if i = j then u i else 0

theorem tensorProd_diag (u : m → R) (v : n → R) :
    tensorProd (diagMat u) (diagMat v) = diagMat (fun p => u p.1 * v p.2) := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [tensorProd, diagMat]
  by_cases hi : i₁ = i₂ <;> by_cases hj : j₁ = j₂
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]
  · simp [hi, hj]

theorem prod_tensor_spectrum (u : m → R) (v : n → R) :
    (∏ p : m × n, (u p.1 * v p.2)) = (∏ i, u i) ^ dimN * (∏ j, v j) ^ dimM := by
  rw [Fintype.prod_prod_type]
  have h_inner (i : m) : (∏ j : n, (u i * v j)) = u i ^ dimN * (∏ j : n, v j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [h_inner]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]

def spectralLogDet (u : m → ℝ) : ℝ :=
  ∑ i, Real.log (u i)

def spectralBarrier (u : m → ℝ) : ℝ :=
  - spectralLogDet u

theorem spectral_barrier_tensor_additivity
    (u : m → ℝ) (v : n → ℝ)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) :
    spectralBarrier (fun (p : m × n) => u p.1 * v p.2) =
      (dimN : ℝ) * spectralBarrier u + (dimM : ℝ) * spectralBarrier v := by
  dsimp [spectralBarrier, spectralLogDet]
  have h_prod_log :
      (∑ p : m × n, Real.log (u p.1 * v p.2)) =
        (dimN : ℝ) * (∑ i, Real.log (u i)) + (dimM : ℝ) * (∑ j, Real.log (v j)) := by
    have h_split (p : m × n) : Real.log (u p.1 * v p.2) = Real.log (u p.1) + Real.log (v p.2) :=
      Real.log_mul (ne_of_gt (hu p.1)) (ne_of_gt (hv p.2))
    simp_rw [h_split]
    rw [Fintype.sum_prod_type]
    have h_inner (i : m) :
        (∑ j : n, (Real.log (u i) + Real.log (v j))) =
          (dimN : ℝ) * Real.log (u i) + ∑ j : n, Real.log (v j) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp_rw [h_inner]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h_prod_log]
  ring

end InfoGeometry.Modular.Tensor

end noncomputable section
