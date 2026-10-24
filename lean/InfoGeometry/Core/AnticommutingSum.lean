/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.NoncommRing

/-! # Squares of finite anticommuting linear combinations

No cancellation of two is used. In particular, square-zero must be supplied
separately from self-anticommutation in characteristic two.
-/
namespace InfoGeometry.Core.AnticommutingSum
open scoped BigOperators

variable {A : Type*} [Ring A] {ι : Type*}

/-- All mixed terms cancel pairwise, over an arbitrary associative ring. -/
theorem sum_square (s : Finset ι) (g : ι → A)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i * g j + g j * g i = 0) :
    (∑ i ∈ s, g i) * (∑ i ∈ s, g i) = ∑ i ∈ s, g i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i * g j + g j * g i = 0 :=
      fun i hi j hj hij => hanti i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hx : g a * (∑ i ∈ s, g i) + (∑ i ∈ s, g i) * g a = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero (fun i hi => hanti a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (ne_of_mem_of_not_mem hi ha).symm)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc
      (g a + ∑ i ∈ s, g i) * (g a + ∑ i ∈ s, g i) =
          g a * g a + (g a * (∑ i ∈ s, g i) + (∑ i ∈ s, g i) * g a) +
            (∑ i ∈ s, g i) * (∑ i ∈ s, g i) := by noncomm_ring
      _ = g a * g a + ∑ i ∈ s, g i * g i := by rw [hx, add_zero, ih hs]

variable {R : Type*} [CommRing R] [Algebra R A]

/-- Central scalar coefficients preserve the off-diagonal anticommutation laws. -/
theorem smul_anti (r s : R) {a b : A} (hab : a * b + b * a = 0) :
    (r • a) * (s • b) + (s • b) * (r • a) = 0 := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm s r, ← smul_add, hab, smul_zero]

variable [Fintype ι]

/-- The native basis extension squares to the weighted sum-of-squares form. -/
theorem basis_square (g : ι → A) (w : ι → R)
    (hanti : ∀ i j, i ≠ j → g i * g j + g j * g i = 0)
    (hsq : ∀ i, g i * g i = algebraMap R A (w i)) (x : ι → R) :
    ((Pi.basisFun R ι).constr R g x) * ((Pi.basisFun R ι).constr R g x) =
      algebraMap R A (QuadraticMap.weightedSumSquares R w x) := by
  have he : (Pi.basisFun R ι).constr R g x = ∑ i, x i • g i := by
    simp [Module.Basis.constr_apply_fintype]
  rw [he, sum_square _ _ (fun i _ j _ hij => smul_anti _ _ (hanti i j hij))]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_smul_comm, hsq, Algebra.smul_def, ← map_mul]
  congr 1
  exact mul_comm _ _

/-- Native basis extension of pairwise anticommuting square-zero generators. -/
theorem basis_square_zero (g : ι → A)
    (hanti : ∀ i j, i ≠ j → g i * g j + g j * g i = 0)
    (hsq : ∀ i, g i * g i = 0) (x : ι → R) :
    ((Pi.basisFun R ι).constr R g x) * ((Pi.basisFun R ι).constr R g x) = 0 := by
  have H := basis_square g (fun _ => (0 : R)) hanti
    (fun i => by simpa only [map_zero] using hsq i) x
  simpa using H

/-- The CAR pairing of finite linear combinations is the coefficient pairing. -/
theorem mixed_sum_car [DecidableEq ι] (g k : ι → A)
    (hcar : ∀ i j, g i * k j + k j * g i = if i = j then 1 else 0)
    (x y : ι → R) :
    (∑ i, x i • g i) * (∑ j, y j • k j) +
      (∑ j, y j • k j) * (∑ i, x i • g i) = algebraMap R A (∑ i, x i * y i) := by
  classical
  have hswap : (∑ j, ∑ i, (x i • g i) * (y j • k j)) =
      ∑ i, ∑ j, (x i • g i) * (y j • k j) := Finset.sum_comm
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [hswap, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have hterm : ∀ i j, (x i • g i) * (y j • k j) + (y j • k j) * (x i • g i) =
      if i = j then algebraMap R A (x i * y j) else 0 := by
    intro i j
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (y j) (x i), ← smul_add, hcar]
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  simp_rw [hterm]
  simp [map_sum]

end InfoGeometry.Core.AnticommutingSum
