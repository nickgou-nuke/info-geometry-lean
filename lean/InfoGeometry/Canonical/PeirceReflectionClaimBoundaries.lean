/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-! Counterexamples to unconditional reflection interpretations.
Self-adjointness does not imply a square-one law. Nonzero wall coefficients
do not imply a nonzero reflection defect over rings with two-torsion. -/
namespace InfoGeometry.Canonical.PeirceReflectionClaimBoundaries

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

theorem selfAdjoint_not_square_one :
    IsSelfAdjoint (2 • (1 : Mat2Z)) ∧
      (2 • (1 : Mat2Z)) * (2 • (1 : Mat2Z)) ≠ 1 := by
  constructor
  · simp [IsSelfAdjoint]
  · intro h
    have he := congrFun (congrFun h 0) 0
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] at he

abbrev Mat2Six := Matrix (Fin 2) (Fin 2) (ZMod 6)
def d : Mat2Six := !![0,1;0,0]
def b : Mat2Six := !![0,0;1,0]
def reflection : Mat2Six := d+b
def wheel : Mat2Six := d-b
def wall : Mat2Six := (1 : ZMod 6) • reflection + (3 : ZMod 6) • wheel

theorem six_seed_pair : d*d=0 ∧ b*b=0 ∧ d*b*d=d ∧ b*d*b=b := by decide

theorem six_noncommuting : d*b ≠ b*d := by decide

/-- Both coefficients and the wall are nonzero, but the wall is invariant. -/
theorem nonzero_wall_can_be_reflection_invariant :
    (1 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ wall ≠ 0 ∧
      reflection * wall * reflection = wall := by decide

/-- The defect criterion itself requires no scalar cancellation hypothesis. -/
theorem defect_zero_iff {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (q w j : A) (β : R) (h : q*w*q-w = -((2*β) • j)) :
    q*w*q = w ↔ (2*β) • j = 0 := by
  rw [← sub_eq_zero, h, neg_eq_zero]

end InfoGeometry.Canonical.PeirceReflectionClaimBoundaries
