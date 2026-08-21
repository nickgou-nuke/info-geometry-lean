import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

noncomputable section

open Matrix
open BigOperators
open Finset

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
  calc
    (∑ i, A₁ i₁ i * A₂ i i₂) * (∑ j, B₁ j₁ j * B₂ j j₂) =
      ∑ i, (A₁ i₁ i * A₂ i i₂) * (∑ j, B₁ j₁ j * B₂ j j₂) := by rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (A₁ i₁ i * A₂ i i₂) * (B₁ j₁ j * B₂ j j₂) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, (A₁ i₁ i * B₁ j₁ j) * (A₂ i i₂ * B₂ j j₂) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring

@[simp]
theorem tensorProd_one :
    tensorProd (1 : Matrix m m R) (1 : Matrix n n R) = 1 := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [tensorProd]
  by_cases h1 : i₁ = i₂
  · by_cases h2 : j₁ = j₂
    · subst h1; subst h2; simp [Matrix.one_apply]
    · have : ¬(i₁, j₁) = (i₂, j₂) := by intro heq; injection heq with _ h; exact h2 h
      simp [h2, this, Matrix.one_apply]
  · have : ¬(i₁, j₁) = (i₂, j₂) := by intro heq; injection heq with h _; exact h1 h
    simp [h1, this, Matrix.one_apply]

theorem tensorProd_trace (A : Matrix m m R) (B : Matrix n n R) :
    Matrix.trace (tensorProd A B) = Matrix.trace A * Matrix.trace B := by
  dsimp [tensorProd, Matrix.trace]
  rw [Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, A i i * B j j) = ∑ i, A i i * (∑ j, B j j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.mul_sum]
    _ = (∑ i, A i i) * (∑ j, B j j) := by
      rw [← Finset.sum_mul]

def diagMat (u : m → R) : Matrix m m R :=
  fun i j => if i = j then u i else 0

theorem tensorProd_diag (u : m → R) (v : n → R) :
    tensorProd (diagMat u) (diagMat v) = diagMat (fun ⟨i, j⟩ => u i * v j) := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  dsimp [tensorProd, diagMat]
  by_cases h1 : i₁ = i₂
  · by_cases h2 : j₁ = j₂
    · subst h1; subst h2; simp
    · have : ¬(i₁, j₁) = (i₂, j₂) := by intro heq; injection heq with _ h; exact h2 h
      simp [h2, this]
  · have : ¬(i₁, j₁) = (i₂, j₂) := by intro heq; injection heq with h _; exact h1 h
    simp [h1, this]

theorem prod_tensor_spectrum (u : m → R) (v : n → R) :
    (∏ p : m × n, (u p.1 * v p.2)) = (∏ i, u i) ^ dimN * (∏ j, v j) ^ dimM := by
  rw [Fintype.prod_prod_type]
  have h_inner (i : m) : (∏ j : n, (u i * v j)) = u i ^ dimN * (∏ j : n, v j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ]
  simp_rw [h_inner]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Finset.prod_pow]

def spectralLogDet {k : Type*} [Fintype k] (u : k → ℝ) : ℝ :=
  ∑ i, Real.log (u i)

def spectralBarrier {k : Type*} [Fintype k] (u : k → ℝ) : ℝ :=
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
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    simp_rw [h_inner]
    rw [sum_add_distrib]
    have h_sum1 : (∑ x, (dimN : ℝ) * Real.log (u x)) = (dimN : ℝ) * (∑ x, Real.log (u x)) := by
      rw [← mul_sum]
    have h_sum2 : (∑ _x : m, (∑ j : n, Real.log (v j))) = (dimM : ℝ) * (∑ j : n, Real.log (v j)) := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    rw [h_sum1, h_sum2]
  rw [h_prod_log]
  ring

end InfoGeometry.Modular.Tensor

end noncomputable section
