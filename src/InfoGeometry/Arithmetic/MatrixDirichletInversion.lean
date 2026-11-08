/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
# Dirichlet inversion with noncommutative matrix coefficients

Dependency order: matrix multiplication → ordered Dirichlet convolution →
zeta/Möbius inverse kernels → recovery of arbitrary matrix-valued data.
The convolution unit is the discrete impulse at the integer 1. It is not
a Dirac distribution or an assertion about analytic zeta series.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MatrixDirichletInversion

open ArithmeticFunction

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev MatrixData (n : Type*) [Fintype n] [DecidableEq n] :=
  ArithmeticFunction (Matrix n n ℂ)

/-- Left Möbius inversion recovers arbitrary matrix coefficients. -/
theorem recover_left (F : MatrixData n) :
    (moebius : MatrixData n) * ((zeta : MatrixData n) * F) = F := by
  rw [← mul_assoc, coe_moebius_mul_coe_zeta, one_mul]

/-- Right inversion preserves the order of the operator factors. -/
theorem recover_right (F : MatrixData n) :
    (F * (zeta : MatrixData n)) * (moebius : MatrixData n) = F := by
  rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

/-- Zeta convolution loses no matrix-valued data. -/
theorem zeta_mul_injective :
    Function.Injective (fun F : MatrixData n => (zeta : MatrixData n) * F) := by
  intro F G h
  have h' := congrArg (fun H : MatrixData n => (moebius : MatrixData n) * H) h
  simpa only [recover_left] using h'

/-- The discrete delta is identity at 1 and zero at the other integers. -/
theorem mobius_zeta_delta (k : ℕ) :
    ((moebius : MatrixData n) * (zeta : MatrixData n)) k =
      if k = 1 then (1 : Matrix n n ℂ) else 0 := by
  rw [coe_moebius_mul_coe_zeta, one_apply]

/-- Logarithmic divisor weights are the zeta sum of prime-power weights,
acting on arbitrary matrix-valued data. -/
theorem zeta_mangoldt_action (F : MatrixData n) :
    (zeta : ArithmeticFunction ℝ) • (vonMangoldt • F) = log • F := by
  rw [← mul_smul, zeta_mul_vonMangoldt]

/-- Möbius inversion of logarithmic weights recovers von Mangoldt weights
without restricting the matrix coefficients to a commutative subalgebra. -/
theorem moebius_log_action (F : MatrixData n) :
    (moebius : ArithmeticFunction ℝ) • (log • F) = vonMangoldt • F := by
  rw [← mul_smul, moebius_mul_log_eq_vonMangoldt]

/-- Embed a full matrix as a coefficient supported at the convolution unit. -/
def impulse (A : Matrix n n ℂ) : MatrixData n where
  toFun k := if k = 1 then A else 0
  map_zero' := by simp

@[simp] theorem impulse_one (A : Matrix n n ℂ) : impulse A 1 = A := by
  simp [impulse]

/-- Convolution with the arithmetic zeta function turns an impulse at one
into the constant coefficient `A` at every positive index.  This is the
divisor-sum action of zeta, stated for matrix-valued coefficients. -/
theorem zeta_mul_impulse_apply {A : Matrix n n ℂ} {k : ℕ} (hk : k ≠ 0) :
    ((zeta : MatrixData n) * impulse A) k = A := by
  rw [coe_zeta_mul_apply]
  simp only [impulse]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro i hi hne
    simp [hne]
  · intro hnot
    exfalso
    apply hk
    simpa using hnot

@[simp] theorem impulse_add (A B : Matrix n n ℂ) :
    impulse (A + B) = impulse A + impulse B := by
  apply ArithmeticFunction.ext
  intro k
  change (if k = 1 then A + B else 0) =
    (if k = 1 then A else 0) + (if k = 1 then B else 0)
  by_cases hk : k = 1 <;> simp [hk]

@[simp] theorem impulse_zero : impulse (0 : Matrix n n ℂ) = 0 := by
  apply ArithmeticFunction.ext
  intro k
  by_cases hk : k = 1 <;> simp [impulse, hk]

@[simp] theorem impulse_identity : impulse (1 : Matrix n n ℂ) = 1 := by
  apply ArithmeticFunction.ext
  intro k
  by_cases hk : k = 1 <;> simp [impulse, hk, one_apply]

/-- The coefficient-at-one embedding preserves ordered matrix multiplication
under Dirichlet convolution.  Its support is precisely the convolution unit,
so no commutativity of matrix coefficients is used. -/
@[simp] theorem impulse_mul (A B : Matrix n n ℂ) :
    impulse A * impulse B = impulse (A * B) := by
  apply ArithmeticFunction.ext
  intro k
  by_cases hk : k = 1
  · subst k
    simp only [ArithmeticFunction.mul_apply_one, impulse_one]
  · rw [ArithmeticFunction.mul_apply]
    ext i j
    rw [Matrix.sum_apply]
    calc
      (∑ d ∈ k.divisorsAntidiagonal,
          (impulse A d.1 * impulse B d.2) i j) = 0 := by
        apply Finset.sum_eq_zero
        intro (d : ℕ × ℕ) hd
        change ((if d.1 = 1 then A else 0) *
          (if d.2 = 1 then B else 0)) i j = 0
        by_cases hfst : d.1 = 1
        · by_cases hsnd : d.2 = 1
          · have hprod := (Nat.mem_divisorsAntidiagonal.mp hd).1
            exact (hk (by simpa [hfst, hsnd] using hprod.symm)).elim
          · simp [hsnd]
        · simp [hfst]
      _ = (impulse (A * B) k) i j := by simp [impulse, hk]

/-- The matrix algebra embeds as the convolution-unit-supported subalgebra of
matrix-valued arithmetic functions. -/
def impulseRingHom : Matrix n n ℂ →+* MatrixData n where
  toFun := impulse
  map_one' := impulse_identity
  map_mul' := by
    intro A B
    exact (impulse_mul A B).symm
  map_zero' := impulse_zero
  map_add' := impulse_add

/-- Evaluation at the convolution unit makes the impulse ring hom injective. -/
theorem impulseRingHom_injective : Function.Injective (impulseRingHom (n := n)) := by
  intro A B h
  change impulse A = impulse B at h
  have h₁ := congrArg (fun F : MatrixData n => F 1) h
  simpa only [impulse_one] using h₁

/-- A noncommuting pair of matrices remains noncommuting under convolution. -/
theorem impulse_noncommuting {A B : Matrix n n ℂ} (h : A * B ≠ B * A) :
    impulse A * impulse B ≠ impulse B * impulse A := by
  intro he
  have h1 := congrArg (fun F : MatrixData n => F 1) he
  exact h (by simpa only [mul_apply_one, impulse_one] using h1)

/-- Every matrix size with two distinct indices has a concrete pair of
noncommuting Dirichlet data, using off-diagonal matrix units. -/
theorem exists_noncommuting (i j : n) (hij : i ≠ j) :
    ∃ F G : MatrixData n, F * G ≠ G * F := by
  refine ⟨impulse (Matrix.single i j 1), impulse (Matrix.single j i 1),
    impulse_noncommuting ?_⟩
  intro h
  have he := congrArg (fun A : Matrix n n ℂ => A i i) h
  simp [Matrix.mul_apply, Matrix.single, Ne.symm hij] at he

end InfoGeometry.Arithmetic.MatrixDirichletInversion
