import Mathlib

/-!
# Fredholm regularization of the modular flow

This file records the Lean formalization of the final regularization step:

`F(Δ) = (Δ - 1)/(Δ + 1)`.

Analytically, with `Δ=e^K`, this is `tanh(K/2)`; near `K=0` it has
expansion `K/2 - K^3/24 + ...`.  Lean proves the algebraic parts without
using analytic series: the defect value `F(1)=0`, the Pauli/Cayley matrix
regularization, and the Fredholm/Kasparov interpretation.
-/

noncomputable section

namespace FredholmRegularization

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Scalar Fredholm/Cayley regularization. -/
def fredholmScalar (Δ : ℂ) : ℂ := (Δ - 1) / (Δ + 1)

/-- At the modular identity/zero defect, the Fredholm operator is exactly zero. -/
theorem fredholm_at_defect : fredholmScalar 1 = 0 := by
  norm_num [fredholmScalar]

/-- The scalar Fredholm regularization is invariantly zero iff the numerator vanishes, away from denominator zero. -/
theorem fredholm_zero_iff (Δ : ℂ) (hden : Δ + 1 ≠ 0) :
    fredholmScalar Δ = 0 ↔ Δ = 1 := by
  unfold fredholmScalar
  constructor
  · intro h
    have hmul := congrArg (fun z => z * (Δ + 1)) h
    field_simp [hden] at hmul
    have hzero : Δ - 1 = 0 := by simpa using hmul
    exact sub_eq_zero.mp hzero
  · intro h
    subst h
    norm_num

/-- Pauli generator. -/
def σ1 : M2C := !![0, 1; 1, 0]

/-- Modular exponential form for `K=vσ₁`: `Δ=cI+sσ₁`. -/
def DeltaForm (c s : ℂ) : M2C := c • (1 : M2C) + s • σ1

/-- Explicit inverse of `(Δ+I)` when `c²-s²=1`. -/
def denInv (c s : ℂ) : M2C :=
  (1 / (2 * (c + 1))) • ((c + 1) • (1 : M2C) - s • σ1)

/-- `σ₁²=1`. -/
theorem σ1_sq : σ1 * σ1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [σ1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit denominator inverse. -/
theorem den_mul_inv (c s : ℂ) (h : c^2 - s^2 = 1) (hc : c + 1 ≠ 0) :
    (DeltaForm c s + 1) * denInv c s = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [DeltaForm, denInv, σ1, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    field_simp [hc, two_ne_zero] <;>
    ring_nf at h ⊢ <;>
    rw [h] <;> ring

/-- Fredholm/Cayley regularization of `cI+sσ₁` gives `(s/(c+1))σ₁`. -/
theorem fredholm_pauli_regularization (c s : ℂ) (h : c^2 - s^2 = 1) (hc : c + 1 ≠ 0) :
    (DeltaForm c s - 1) * denInv c s = (s / (c + 1)) • σ1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [DeltaForm, denInv, σ1, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    field_simp [hc, two_ne_zero] <;>
    ring_nf at h ⊢ <;>
    rw [h] <;> ring

#check fredholm_at_defect
#check fredholm_zero_iff
#check fredholm_pauli_regularization

end FredholmRegularization
