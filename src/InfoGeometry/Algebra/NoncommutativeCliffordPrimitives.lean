/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Shared Noncommutative $Cl(1,1)$ & Inductive Tower Primitives

Canonical owner of the division-free $2 \times 2$ matrix constructor `mat2`, extensionality
`ext_fin2`, `Matrix (Fin 2) (Fin 2) A` entry-level `simp` lemmas, the $Cl(1,1)$ basis generators
(`gamma1Op`, `sigmaOp`, `omegaOp`, `P_plus`, `F_plus`, `F_minus`, `N_plus`, `fiberEmbed`,
`kleinTwist`), and the inductive Bott–Clifford matrix tower `ClTower A n`.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeCliffordPrimitives

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => a
    | 0, 1 => b
    | 1, 0 => c
    | 1, 1 => d

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

@[simp] lemma mat2_00 {A : Type*} (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 {A : Type*} (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 {A : Type*} (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 {A : Type*} (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma tr2_00 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 0 = M 0 0 := rfl
@[simp] lemma tr2_01 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 1 = M 1 0 := rfl
@[simp] lemma tr2_10 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 0 = M 0 1 := rfl
@[simp] lemma tr2_11 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 1 = M 1 1 := rfl

@[simp] lemma ct2_00 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

variable {A : Type*} [Ring A]

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def F_plus     : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def N_plus     : Matrix (Fin 2) (Fin 2) A := mat2 (-1) (-1) 1 1
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def kleinTwist (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 (-a)

end Matrix2Simp

universe u

@[reducible] def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

@[reducible] instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

@[reducible] instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
