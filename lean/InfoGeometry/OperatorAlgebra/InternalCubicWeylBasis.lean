/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.SylvesterWeylBraidBridge
import InfoGeometry.Algebra.IsotropicCyclotomicGalois
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Basic.Real.Basic

/-!
# Cubic Weyl bases with noncommutative coefficients

The existing clock and shift give a native basis of the full three-by-three
matrix module over a real coefficient algebra. The cubic phase belongs to
that coefficient ring and need not be central. Fourier factors multiply
entries on the right; the resulting coordinate map is left-linear over the
entire coefficient ring. Only the normalization by `1/3` is a central real
scalar. This algebraic basis does not assert orthonormality for any adjoint.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.InternalCubicWeylBasis

open scoped BigOperators
open InfoGeometry.Algebra.IsotropicCyclotomicGalois

section Shift

variable {R : Type*} [Ring R] (n : ℕ) [NeZero n]

/-- The existing cyclic shift translates the row without reordering entries. -/
theorem shift_mul_apply (X : Matrix (ZMod n) (ZMod n) R) (i j : ZMod n) :
    (SylvesterWeylBraid.shiftMatrix n (R := R) * X) i j = X (i - 1) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - 1)]
  · simp [SylvesterWeylBraid.shiftMatrix]
  · intro k _ hk
    have hne : i ≠ k + 1 := by
      intro h
      exact hk ((eq_sub_iff_add_eq).2 h.symm)
    simp [SylvesterWeylBraid.shiftMatrix, hne]
  · intro h
    exact (h (Finset.mem_univ (i - 1))).elim

/-- The cyclic support formula for every power of the actual shift. -/
theorem shift_pow_apply (k : ℕ) (i j : ZMod n) :
    (SylvesterWeylBraid.shiftMatrix n (R := R) ^ k) i j =
      if i = j + (k : ZMod n) then 1 else 0 := by
  induction k generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ', shift_mul_apply, ih]
    have hindex : i - 1 = j + (k : ZMod n) ↔
        i = j + ((k + 1 : ℕ) : ZMod n) := by
      rw [sub_eq_iff_eq_add]
      simp [Nat.cast_add, add_assoc]
    simp only [hindex]

end Shift

variable {R : Type*} [Ring R]

/-- The internal cubic character, with a residue represented by `0`, `1`, or `2`. -/
def phasePower (q : R) (a : ZMod 3) : R := q ^ a.val

private theorem cube_eq_one (q : R) (hq : cyclo3 q = 0) : q ^ 3 = 1 := by
  simpa only [pow_succ, pow_zero, one_mul] using cyclo3_root_cube q hq

theorem phasePower_add (q : R) (hq : cyclo3 q = 0) (a b : ZMod 3) :
    phasePower q a * phasePower q b = phasePower q (a + b) := by
  unfold phasePower
  rw [← pow_add, ZMod.val_add]
  exact SylvesterWeylBraid.pow_eq_pow_mod 3 q (cube_eq_one q hq) _

private theorem sum_three (f : ZMod 3 → R) :
    ∑ j, f j = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

/-- Finite Fourier cancellation follows from the cubic cyclotomic equation. -/
theorem phasePower_sum (q : R) (hq : cyclo3 q = 0) (d : ZMod 3) :
    ∑ j : ZMod 3, phasePower q (j * d) = if d = 0 then 3 else 0 := by
  have hsum : 1 + q + q ^ 2 = 0 := by
    calc
      1 + q + q ^ 2 = cyclo3 q := by unfold cyclo3; noncomm_ring
      _ = 0 := hq
  have hcases : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = 2 := by decide
  rcases hcases d with rfl | rfl | rfl
  · norm_num [sum_three, phasePower]
  · norm_num [sum_three, phasePower, ZMod.val_one_eq_one_mod, ZMod.val_ofNat]
    exact hsum
  · have hsum' : 1 + q ^ 2 + q = 0 := by
      calc
        1 + q ^ 2 + q = 1 + q + q ^ 2 := by abel
        _ = 0 := hsum
    have h20 : (2 : ZMod 3) ≠ 0 := by decide
    norm_num [sum_three, phasePower, ZMod.val_one_eq_one_mod, ZMod.val_ofNat, h20]
    exact hsum'

/-- Ordered character pairing; no arbitrary coefficient commutes past a phase. -/
theorem phasePower_pair_sum (q : R) (hq : cyclo3 q = 0) (j k : ZMod 3) :
    ∑ b : ZMod 3, phasePower q (-(b * j)) * phasePower q (b * k) =
      if j = k then 3 else 0 := by
  simp_rw [phasePower_add q hq]
  have hexp (b : ZMod 3) : -(b * j) + b * k = b * (k - j) := by ring
  simp_rw [hexp]
  rw [phasePower_sum q hq]
  simp [sub_eq_zero, eq_comm]

/-- The reverse Fourier pairing has the same Kronecker normalization. -/
theorem phasePower_pair_sum_rev (q : R) (hq : cyclo3 q = 0) (j k : ZMod 3) :
    ∑ b : ZMod 3, phasePower q (j * b) * phasePower q (-(k * b)) =
      if j = k then 3 else 0 := by
  simp_rw [phasePower_add q hq]
  have hexp (b : ZMod 3) : j * b + -(k * b) = b * (j - k) := by ring
  simp_rw [hexp]
  rw [phasePower_sum q hq]
  simp [sub_eq_zero]

/-- The words use precisely the existing shift-then-clock convention. -/
def weylWord (q : R) (ab : ZMod 3 × ZMod 3) : Matrix (ZMod 3) (ZMod 3) R :=
  SylvesterWeylBraid.shiftMatrix 3 ^ ab.1.val *
    SylvesterWeylBraid.clockMatrix 3 q ^ ab.2.val

theorem weylWord_apply (q : R) (hq : cyclo3 q = 0)
    (a b i j : ZMod 3) :
    weylWord q (a, b) i j = if i = j + a then phasePower q (b * j) else 0 := by
  change (SylvesterWeylBraid.shiftMatrix 3 (R := R) ^ a.val *
    Matrix.diagonal (fun j : ZMod 3 => q ^ j.val) ^ b.val) i j = _
  rw [Matrix.diagonal_pow, Matrix.mul_diagonal, shift_pow_apply]
  simp only [ZMod.natCast_zmod_val, Pi.pow_apply]
  split_ifs
  · rw [one_mul, ← pow_mul, Nat.mul_comm]
    unfold phasePower
    rw [ZMod.val_mul]
    exact SylvesterWeylBraid.pow_eq_pow_mod 3 q (cube_eq_one q hq) _
  · rw [zero_mul]

variable [Algebra ℝ R]

/-- Right multiplication by the internal phase extracts left-module coordinates. -/
def fourier (q : R) (f : ZMod 3 → R) (b : ZMod 3) : R :=
  (1 / 3 : ℝ) • ∑ j : ZMod 3, f j * phasePower q (-(b * j))

/-- The inverse transform keeps all coefficient factors on the left. -/
def inverseFourier (q : R) (c : ZMod 3 → R) (j : ZMod 3) : R :=
  ∑ b : ZMod 3, c b * phasePower q (b * j)

theorem inverseFourier_fourier (q : R) (hq : cyclo3 q = 0) (f : ZMod 3 → R) :
    inverseFourier q (fourier q f) = f := by
  funext k
  unfold inverseFourier fourier
  simp_rw [smul_mul_assoc, Finset.sum_mul, mul_assoc]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, phasePower_pair_sum q hq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show f k * (3 : R) = f k + f k + f k by noncomm_ring]
  module

theorem fourier_inverseFourier (q : R) (hq : cyclo3 q = 0) (c : ZMod 3 → R) :
    fourier q (inverseFourier q c) = c := by
  funext b
  unfold fourier inverseFourier
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, phasePower_pair_sum_rev q hq]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show c b * (3 : R) = c b + c b + c b by noncomm_ring]
  module

/-- Explicit left-linear coordinates along the cyclic matrix diagonals. -/
def coordinates (q : R) (X : Matrix (ZMod 3) (ZMod 3) R)
    (ab : ZMod 3 × ZMod 3) : R :=
  fourier q (fun j => X (j + ab.1) j) ab.2

/-- The inverse coordinate map, expressed directly at each matrix entry. -/
def synthesis (q : R) (c : (ZMod 3 × ZMod 3) → R) : Matrix (ZMod 3) (ZMod 3) R :=
  fun i j => inverseFourier q (fun b => c (i - j, b)) j

theorem synthesis_coordinates (q : R) (hq : cyclo3 q = 0)
    (X : Matrix (ZMod 3) (ZMod 3) R) : synthesis q (coordinates q X) = X := by
  ext i j
  change inverseFourier q (fourier q (fun k => X (k + (i - j)) k)) j = X i j
  rw [inverseFourier_fourier q hq]
  simp

theorem coordinates_synthesis (q : R) (hq : cyclo3 q = 0)
    (c : (ZMod 3 × ZMod 3) → R) : coordinates q (synthesis q c) = c := by
  funext ab
  simp only [coordinates, synthesis, add_sub_cancel_left]
  exact congrFun (fourier_inverseFourier q hq (fun b => c (ab.1, b))) ab.2

/-- A native coordinate equivalence over the full, possibly noncommutative ring. -/
def coordinateEquiv (q : R) (hq : cyclo3 q = 0) :
    Matrix (ZMod 3) (ZMod 3) R ≃ₗ[R] ((ZMod 3 × ZMod 3) → R) where
  toFun := coordinates q
  invFun := synthesis q
  left_inv := synthesis_coordinates q hq
  right_inv := coordinates_synthesis q hq
  map_add' X Y := by
    funext ab
    simp [coordinates, fourier, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' r X := by
    funext ab
    simp only [coordinates, fourier, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_smul_comm, RingHom.id_apply]

/-- The actual nine-word basis as a native left-module basis. -/
def weylBasis (q : R) (hq : cyclo3 q = 0) :
    Module.Basis (ZMod 3 × ZMod 3) R (Matrix (ZMod 3) (ZMod 3) R) :=
  Module.Basis.ofEquivFun (coordinateEquiv q hq)

theorem weylBasis_apply (q : R) (hq : cyclo3 q = 0) (ab : ZMod 3 × ZMod 3) :
    weylBasis q hq ab = weylWord q ab := by
  rw [weylBasis, Module.Basis.coe_ofEquivFun]
  change synthesis q (Pi.single ab 1) = weylWord q ab
  rcases ab with ⟨a, b⟩
  ext i j
  rw [weylWord_apply q hq]
  by_cases h : i = j + a
  · simp [synthesis, inverseFourier, Pi.single_apply, h]
  · have hindex : a ≠ i - j := by
      intro heq
      apply h
      rw [heq]
      abel
    simp [synthesis, inverseFourier, h, hindex]

/-- The native basis coordinates are the ordered Fourier formula. -/
theorem weylBasis_repr_apply (q : R) (hq : cyclo3 q = 0)
    (X : Matrix (ZMod 3) (ZMod 3) R) (ab : ZMod 3 × ZMod 3) :
    (weylBasis q hq).repr X ab =
      (1 / 3 : ℝ) • ∑ j : ZMod 3, X (j + ab.1) j * phasePower q (-(ab.2 * j)) := rfl

/-- Every full matrix is reconstructed with left operator-valued coefficients. -/
theorem weyl_reconstruction (q : R) (hq : cyclo3 q = 0)
    (X : Matrix (ZMod 3) (ZMod 3) R) :
    ∑ ab, coordinates q X ab • weylWord q ab = X := by
  simpa only [weylBasis_apply, weylBasis_repr_apply, coordinates, fourier] using
    (weylBasis q hq).sum_repr X

end InfoGeometry.OperatorAlgebra.InternalCubicWeylBasis
