/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.MajoranaVacuumWickFour
import InfoGeometry.Algebra.CliffordBraidingInterfaces
import InfoGeometry.Algebra.FourthRootClockShift
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A Majorana quartet and the four-state clock generate the same algebra

The existing Jordan--Wigner matrices and the existing four-state clock/shift
are related by explicit ordered polynomial formulas in both directions.
The resulting equality is an equality of native complex subalgebras of
`Matrix (Fin 4) (Fin 4) ℂ`. It is a finite operator re-encoding; it does not
assert locality, a phase transition, a protected edge mode, or braid dynamics.

For the convention `α₂ α₁ = i α₁ α₂`, take `α₁ = cyclicShift` and
`α₂ = degreeClock`. Their exchange law and fourth powers are already proved
in `FourthRootPeirceProjectors`.
-/

noncomputable section

namespace InfoGeometry.Algebra.MajoranaClockReencoding

open InfoGeometry.Quantum.MajoranaVacuumWickFour (Mat4C gamma)
open InfoGeometry.Algebra.FourthRootPeirceProjectors
  (degreeClock cyclicShift phase degreeClock_fourth cyclicShift_fourth)

theorem gamma_square (i : Fin 4) : gamma i * gamma i = 1 := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [gamma, Matrix.mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 1000000 in
theorem gamma_anticommute (i j : Fin 4) (hij : i ≠ j) :
    gamma i * gamma j = -(gamma j * gamma i) := by
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact (hij rfl).elim
    | (ext a b
       fin_cases a <;> fin_cases b <;>
         norm_num [gamma, Matrix.mul_apply, Fin.sum_univ_four])

theorem gamma_isSelfAdjoint (i : Fin 4) : IsSelfAdjoint (gamma i) := by
  change star (gamma i) = gamma i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [gamma, Matrix.star_apply]

/-- The existing four matrices satisfy every field of the existing CAR interface. -/
def majoranaSystem : MajoranaSystem 4 Mat4C where
  gamma := gamma
  square_one := gamma_square
  anti_comm := gamma_anticommute

/-- First-site fermion parity, computed from the first Majorana pair. -/
def firstParity : Mat4C := (-Complex.I) • (gamma 0 * gamma 1)

/-- Second-site fermion parity, computed from the second Majorana pair. -/
def secondParity : Mat4C := (-Complex.I) • (gamma 2 * gamma 3)

/-- The two second-site parity projections used in the explicit re-encoding. -/
def secondEven : Mat4C := (1 / 2 : ℂ) • (1 + secondParity)

def secondOdd : Mat4C := (1 / 2 : ℂ) • (1 - secondParity)

/-- Removing the first-site Jordan--Wigner parity string. -/
def secondFlip : Mat4C := firstParity * gamma 2

theorem degreeClock_eq_majorana :
    degreeClock = firstParity * (secondEven + Complex.I • secondOdd) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, phase, firstParity, secondEven, secondOdd,
      secondParity, gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem cyclicShift_eq_majorana :
    cyclicShift = secondFlip * secondEven + gamma 0 * secondFlip * secondOdd := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicShift, secondFlip, firstParity, secondEven, secondOdd,
      secondParity, gamma, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four]

/-- The first Majorana is recovered by squaring the four-cycle. -/
theorem cyclicShift_sq : cyclicShift ^ 2 = gamma 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicShift, gamma, pow_two, Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeClock_sq : degreeClock ^ 2 = secondParity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, phase, secondParity, gamma, pow_two,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem firstParity_eq_clock :
    firstParity = degreeClock * (secondEven - Complex.I • secondOdd) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, phase, firstParity, secondEven, secondOdd,
      secondParity, gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem secondFlip_eq_shift :
    secondFlip = cyclicShift * (secondEven + cyclicShift ^ 2 * secondOdd) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicShift, secondFlip, firstParity, secondEven, secondOdd,
      secondParity, gamma, pow_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four]

theorem gamma_one_recover : gamma 1 = Complex.I • (gamma 0 * firstParity) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstParity, gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_two_recover : gamma 2 = firstParity * secondFlip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstParity, secondFlip, gamma, Matrix.mul_apply, Fin.sum_univ_four]

theorem gamma_three_recover :
    gamma 3 = Complex.I • (firstParity * secondFlip * secondParity) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstParity, secondFlip, secondParity, gamma,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Both generating systems generate exactly the same native complex subalgebra. -/
theorem adjoin_majorana_eq_clock_shift :
    Algebra.adjoin ℂ (Set.range gamma) =
      Algebra.adjoin ℂ ({degreeClock, cyclicShift} : Set Mat4C) := by
  apply le_antisymm
  · let B := Algebra.adjoin ℂ ({degreeClock, cyclicShift} : Set Mat4C)
    have hC : degreeClock ∈ B := Algebra.subset_adjoin (by simp)
    have hS : cyclicShift ∈ B := Algebra.subset_adjoin (by simp)
    have hw : secondParity ∈ B := degreeClock_sq ▸ B.pow_mem hC 2
    have hp : secondEven ∈ B := B.smul_mem (B.add_mem B.one_mem hw) (1 / 2 : ℂ)
    have hm : secondOdd ∈ B := B.smul_mem (B.sub_mem B.one_mem hw) (1 / 2 : ℂ)
    have hz : firstParity ∈ B := by
      rw [firstParity_eq_clock]
      exact B.mul_mem hC (B.sub_mem hp (B.smul_mem hm Complex.I))
    have hy : secondFlip ∈ B := by
      rw [secondFlip_eq_shift]
      exact B.mul_mem hS (B.add_mem hp (B.mul_mem (B.pow_mem hS 2) hm))
    have hx : gamma 0 ∈ B := cyclicShift_sq ▸ B.pow_mem hS 2
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hx
    · change gamma 1 ∈ B
      rw [gamma_one_recover]
      exact B.smul_mem (B.mul_mem hx hz) Complex.I
    · change gamma 2 ∈ B
      rw [gamma_two_recover]
      exact B.mul_mem hz hy
    · change gamma 3 ∈ B
      rw [gamma_three_recover]
      exact B.smul_mem (B.mul_mem (B.mul_mem hz hy) hw) Complex.I
  · let B := Algebra.adjoin ℂ (Set.range gamma)
    have hg (i : Fin 4) : gamma i ∈ B := Algebra.subset_adjoin ⟨i, rfl⟩
    have hz : firstParity ∈ B := B.smul_mem (B.mul_mem (hg 0) (hg 1)) (-Complex.I)
    have hw : secondParity ∈ B := B.smul_mem (B.mul_mem (hg 2) (hg 3)) (-Complex.I)
    have hp : secondEven ∈ B := B.smul_mem (B.add_mem B.one_mem hw) (1 / 2 : ℂ)
    have hm : secondOdd ∈ B := B.smul_mem (B.sub_mem B.one_mem hw) (1 / 2 : ℂ)
    have hy : secondFlip ∈ B := B.mul_mem hz (hg 2)
    apply Algebra.adjoin_le
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [degreeClock_eq_majorana]
      exact B.mul_mem hz (B.add_mem hp (B.smul_mem hm Complex.I))
    · rw [Set.mem_singleton_iff.mp ha, cyclicShift_eq_majorana]
      exact B.add_mem (B.mul_mem hy hp) (B.mul_mem (B.mul_mem (hg 0) hy) hm)

theorem star_degreeClock : star degreeClock = degreeClock ^ 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, phase, Matrix.star_apply, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem star_cyclicShift : star cyclicShift = cyclicShift ^ 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicShift, Matrix.star_apply, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem degreeClock_mem_unitary : degreeClock ∈ unitary Mat4C := by
  rw [Unitary.mem_iff, star_degreeClock]
  constructor
  · simpa only [← pow_succ] using degreeClock_fourth
  · simpa only [← pow_succ'] using degreeClock_fourth

theorem cyclicShift_mem_unitary : cyclicShift ∈ unitary Mat4C := by
  rw [Unitary.mem_iff, star_cyclicShift]
  constructor
  · simpa only [← pow_succ] using cyclicShift_fourth
  · simpa only [← pow_succ'] using cyclicShift_fourth

end InfoGeometry.Algebra.MajoranaClockReencoding
