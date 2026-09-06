/-
Phase 2: Normalized Gell-Mann basis for 𝔰𝔲(3)
- 8 generators λ₁…λ₈ with Tr(λₐλ_b) = 2δ_{ab}
- Structure constants f_{abc}, d_{abc} as computable data
- Commutator/anticommutator formulas
-/
module

import Mathlib
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.SpecialUnitary

open Matrix
open Fin
open Complex
open LieAlgebra

namespace InfoGeometry.Algebra.GellMann

/-- Normalized Gell-Mann matrices λ₁…λ₈ as elements of 𝔰𝔲(3) -/
def λ₁ : su (Fin 3) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₂ : su (Fin 3) :=
  ⟨!![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₃ : su (Fin 3) :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₄ : su (Fin 3) :=
  ⟨!![0, 0, 1; 0, 0, 0; 1, 0, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₅ : su (Fin 3) :=
  ⟨!![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₆ : su (Fin 3) :=
  ⟨!![0, 0, 0; 0, 0, 1; 0, 1, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₇ : su (Fin 3) :=
  ⟨!![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I] <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> norm_num ⟩

def λ₈ : su (Fin 3) :=
  ⟨!![1 / Real.sqrt 3, 0, 0; 0, 1 / Real.sqrt 3, 0; 0, 0, -2 / Real.sqrt 3], by
    constructor
    · -- † = -self
      ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.dagger_apply, Complex.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
      <;> norm_num <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I, Real.sqrt_eq_iff_sq_eq] <;>
      field_simp [Real.sqrt_eq_iff_sq_eq] <;>
      ring_nf <;>
      norm_num <;>
      aesop
    · -- trace = 0
      simp [Matrix.trace, Fin.sum_univ_succ]
      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
      <;> ring_nf
      <;> norm_num ⟩

/-- Array of all 8 Gell-Mann matrices -/
def gellMannArray : Array (su (Fin 3)) :=
  #[λ₁, λ₂, λ₃, λ₄, λ₅, λ₆, λ₇, λ₈]

/-- Get the a-th Gell-Mann matrix (a : Fin 8) -/
def gellMann (a : Fin 8) : su (Fin 3) :=
  gellMannArray a

end InfoGeometry.Algebra.GellMann