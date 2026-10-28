/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Peirce decomposition and tangent geometry of complex matrix idempotents

Every matrix below is arbitrary. No commutativity, diagonal form, or fixed rank is assumed.
The tangent equation is the linear term of the idempotent equation `p * p = p`.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixPeirceZorn.MatrixPeirce

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := Matrix n n ℂ

def complement (p : Mat n) : Mat n := 1 - p

def corner (p q x : Mat n) : Mat n := p * x * q

def positive (p x : Mat n) : Mat n := corner p p x

def negative (p x : Mat n) : Mat n := corner (complement p) (complement p) x

def raise (p x : Mat n) : Mat n := corner p (complement p) x

def lower (p x : Mat n) : Mat n := corner (complement p) p x

def grading (p : Mat n) : Mat n := 2 * p - 1

def number (p x : Mat n) : Mat n := grading p * x - x * grading p

def reflection (p x : Mat n) : Mat n := grading p * x * grading p

/-- Each Peirce corner is a native complex-linear endomorphism of the matrix space. -/
def cornerLinear (p q : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun := corner p q
  map_add' x y := by simp [corner, mul_add, add_mul]
  map_smul' c x := by simp [corner]

@[simp] theorem cornerLinear_apply (p q x : Mat n) : cornerLinear p q x = corner p q x := rfl

omit [Fintype n] in
@[simp] theorem complement_add (p : Mat n) : p + complement p = 1 := by
  simp [complement]

@[simp] theorem complement_idempotent (p : Mat n) (hp : p * p = p) :
    complement p * complement p = complement p := by
  unfold complement
  noncomm_ring [hp]

@[simp] theorem mul_complement (p : Mat n) (hp : p * p = p) :
    p * complement p = 0 := by
  simp [complement, mul_sub, hp]

@[simp] theorem complement_mul (p : Mat n) (hp : p * p = p) :
    complement p * p = 0 := by
  simp [complement, sub_mul, hp]

omit [Fintype n] in
@[simp] theorem complement_complement (p : Mat n) : complement (complement p) = p := by
  simp [complement]

/-- Reconstruction is valid before imposing the idempotent equation. -/
theorem four_corner_decomposition (p x : Mat n) :
    positive p x + raise p x + lower p x + negative p x = x := by
  unfold positive raise lower negative corner complement
  noncomm_ring

omit [DecidableEq n] in
theorem corner_corner (a b c d x : Mat n) :
    corner a b (corner c d x) = (a * c) * x * (d * b) := by
  simp [corner, mul_assoc]

omit [DecidableEq n] in
theorem corner_idempotent (a b x : Mat n) (ha : a * a = a) (hb : b * b = b) :
    corner a b (corner a b x) = corner a b x := by
  rw [corner_corner, ha, hb]
  rfl

omit [DecidableEq n] in
theorem corner_orthogonal_left (a b c d x : Mat n) (h : a * c = 0) :
    corner a b (corner c d x) = 0 := by
  rw [corner_corner, h]
  simp

omit [DecidableEq n] in
theorem corner_orthogonal_right (a b c d x : Mat n) (h : d * b = 0) :
    corner a b (corner c d x) = 0 := by
  rw [corner_corner, h]
  simp

omit [DecidableEq n] in
@[simp] theorem positive_idempotent (p x : Mat n) (hp : p * p = p) :
    positive p (positive p x) = positive p x := corner_idempotent p p x hp hp

@[simp] theorem negative_idempotent (p x : Mat n) (hp : p * p = p) :
    negative p (negative p x) = negative p x :=
  corner_idempotent _ _ x (complement_idempotent p hp) (complement_idempotent p hp)

@[simp] theorem raise_idempotent (p x : Mat n) (hp : p * p = p) :
    raise p (raise p x) = raise p x :=
  corner_idempotent _ _ x hp (complement_idempotent p hp)

@[simp] theorem lower_idempotent (p x : Mat n) (hp : p * p = p) :
    lower p (lower p x) = lower p x :=
  corner_idempotent _ _ x (complement_idempotent p hp) hp

/-- Orthogonal middle idempotents annihilate ordinary products of matching odd corners. -/
theorem corner_mul_zero (a b c d x y : Mat n) (h : b * c = 0) :
    corner a b x * corner c d y = 0 := by
  calc
    corner a b x * corner c d y = a * x * (b * c) * y * d := by simp [corner, mul_assoc]
    _ = 0 := by rw [h]; simp

@[simp] theorem raise_mul_raise (p x y : Mat n) (hp : p * p = p) :
    raise p x * raise p y = 0 := corner_mul_zero _ _ _ _ _ _ (complement_mul p hp)

@[simp] theorem lower_mul_lower (p x y : Mat n) (hp : p * p = p) :
    lower p x * lower p y = 0 := corner_mul_zero _ _ _ _ _ _ (mul_complement p hp)

theorem raise_mul_lower (p x y : Mat n) (hp : p * p = p) :
    raise p x * lower p y = positive p (x * complement p * y) := by
  unfold raise lower positive corner
  calc
    p * x * complement p * (complement p * y * p) =
      p * x * (complement p * complement p) * y * p := by simp [mul_assoc]
    _ = p * (x * complement p * y) * p := by rw [complement_idempotent p hp]; simp [mul_assoc]

theorem lower_mul_raise (p x y : Mat n) (hp : p * p = p) :
    lower p x * raise p y = negative p (x * p * y) := by
  unfold lower raise negative corner
  calc
    complement p * x * p * (p * y * complement p) =
      complement p * x * (p * p) * y * complement p := by simp [mul_assoc]
    _ = complement p * (x * p * y) * complement p := by rw [hp]; simp [mul_assoc]

theorem grading_sq (p : Mat n) (hp : p * p = p) : grading p * grading p = 1 := by
  unfold grading
  noncomm_ring [hp]

/-- The grading commutator is a genuine derivation for ordinary matrix multiplication. -/
theorem number_mul (p x y : Mat n) :
    number p (x * y) = number p x * y + x * number p y := by
  unfold number
  noncomm_ring

theorem number_positive (p x : Mat n) (hp : p * p = p) : number p (positive p x) = 0 := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  unfold number grading positive corner
  noncomm_ring [hp, hp_left]

theorem number_negative (p x : Mat n) (hp : p * p = p) : number p (negative p x) = 0 := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  unfold number grading negative corner complement
  noncomm_ring [hp, hp_left]

theorem number_raise (p x : Mat n) (hp : p * p = p) : number p (raise p x) = 2 * raise p x := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  unfold number grading raise corner complement
  noncomm_ring [hp, hp_left]

theorem number_lower (p x : Mat n) (hp : p * p = p) : number p (lower p x) = -(2 * lower p x) := by
  have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
  unfold number grading lower corner complement
  noncomm_ring [hp, hp_left]

theorem number_eq_odd_difference (p x : Mat n) : number p x = 2 * raise p x - 2 * lower p x := by
  unfold number grading raise lower corner complement
  noncomm_ring

/-- Conjugation by the grading involution preserves multiplication. -/
theorem reflection_mul (p x y : Mat n) (hp : p * p = p) :
    reflection p (x * y) = reflection p x * reflection p y := by
  unfold reflection
  calc
    grading p * (x * y) * grading p = grading p * x * (grading p * grading p) * y * grading p := by
      rw [grading_sq p hp]; simp [mul_assoc]
    _ = grading p * x * grading p * (grading p * y * grading p) := by simp [mul_assoc]

theorem reflection_involutive (p x : Mat n) (hp : p * p = p) :
    reflection p (reflection p x) = x := by
  unfold reflection
  calc
    grading p * (grading p * x * grading p) * grading p =
      (grading p * grading p) * x * (grading p * grading p) := by simp [mul_assoc]
    _ = x := by rw [grading_sq p hp]; simp

theorem reflection_eq_even_sub_odd (p x : Mat n) :
    reflection p x = positive p x + negative p x - raise p x - lower p x := by
  unfold reflection grading positive negative raise lower corner complement
  noncomm_ring

/-- The polynomial idempotent constraint has the indicated first and second order terms. -/
theorem idempotent_expansion (p x : Mat n) (hp : p * p = p) :
    (p + x) * (p + x) - (p + x) = (p * x + x * p - x) + x * x := by
  noncomm_ring [hp]

/-- The tangent space to the matrix idempotent locus is precisely its two off-diagonal corners. -/
theorem tangent_iff_even_corners_zero (p x : Mat n) (hp : p * p = p) :
    p * x + x * p = x ↔ positive p x = 0 ∧ negative p x = 0 := by
  constructor
  · intro h
    have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
    have hmul := congrArg (fun z => p * z) h
    have hpos : positive p x = 0 := by
      unfold positive corner
      have hh : p * x + p * x * p = p * x := by
        simpa only [mul_add, hp_left, ← mul_assoc] using hmul
      exact (add_eq_left.mp hh)
    refine ⟨hpos, ?_⟩
    unfold negative corner complement
    have hh : p * x + x * p - x = 0 := sub_eq_zero.mpr h
    have hpp : p * x * p = 0 := hpos
    calc
      (1 - p) * x * (1 - p) = -(p * x + x * p - x) + p * x * p := by noncomm_ring
      _ = 0 := by rw [hh, hpp]; simp
  · rintro ⟨hpos, hneg⟩
    have hpp : p * x * p = 0 := hpos
    have hqq : (1 - p) * x * (1 - p) = 0 := hneg
    apply sub_eq_zero.mp
    calc
      p * x + x * p - x = p * x * p - (1 - p) * x * (1 - p) := by noncomm_ring
      _ = 0 := by rw [hpp, hqq]; simp

theorem tangent_iff_odd_decomposition (p x : Mat n) (hp : p * p = p) :
    p * x + x * p = x ↔ x = raise p x + lower p x := by
  constructor
  · intro h
    obtain ⟨hpos, hneg⟩ := (tangent_iff_even_corners_zero p x hp).mp h
    have hd := four_corner_decomposition p x
    simpa [hpos, hneg] using hd.symm
  · intro h
    have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
    conv_lhs => rw [h]
    rw [h]
    unfold raise lower corner complement
    noncomm_ring [hp, hp_left]

/-- Every tangent vector is a commutator with the underlying idempotent. -/
theorem tangent_commutator (p x : Mat n) (hp : p * p = p) (hx : p * x + x * p = x) :
    (x * p - p * x) * p - p * (x * p - p * x) = x := by
  have hpp : p * x * p = 0 := ((tangent_iff_even_corners_zero p x hp).mp hx).1
  calc
    (x * p - p * x) * p - p * (x * p - p * x) = x * p + p * x - 2 * (p * x * p) := by
      have hp_left (z : Mat n) : p * (p * z) = p * z := by rw [← mul_assoc, hp]
      noncomm_ring [hp, hp_left]
    _ = x := by rw [hpp]; simpa [add_comm] using hx

omit [DecidableEq n] in
/-- The adjoint reverses the two Peirce corners; this is an operator statement. -/
theorem corner_conjTranspose (p q x : Mat n) :
    (corner p q x)ᴴ = corner qᴴ pᴴ xᴴ := by
  simp [corner, Matrix.conjTranspose_mul, mul_assoc]

omit [Fintype n] in
theorem complement_isHermitian (p : Mat n) (hp : p.IsHermitian) : (complement p).IsHermitian := by
  simpa [complement] using Matrix.isHermitian_one.sub hp

theorem raise_conjTranspose (p x : Mat n) (hp : p.IsHermitian) :
    (raise p x)ᴴ = lower p xᴴ := by
  unfold raise lower
  rw [corner_conjTranspose, hp.eq, (complement_isHermitian p hp).eq]

theorem hermitian_tangent_iff (p x : Mat n) (hp : p * p = p)
    (hps : p.IsHermitian) (hxs : x.IsHermitian) :
    p * x + x * p = x ↔ x = raise p x + (raise p x)ᴴ := by
  rw [raise_conjTranspose p x hps, hxs.eq]
  exact tangent_iff_odd_decomposition p x hp

/-- Off-diagonal matrices have zero trace, without choosing a basis adapted to `p`. -/
theorem trace_raise (p x : Mat n) (hp : p * p = p) : Matrix.trace (raise p x) = 0 := by
  unfold raise corner
  rw [Matrix.trace_mul_comm, ← mul_assoc, complement_mul p hp, zero_mul, Matrix.trace_zero]

theorem trace_lower (p x : Mat n) (hp : p * p = p) : Matrix.trace (lower p x) = 0 := by
  unfold lower corner
  rw [Matrix.trace_mul_comm, ← mul_assoc, mul_complement p hp, zero_mul, Matrix.trace_zero]

theorem tangent_trace_zero (p x : Mat n) (hp : p * p = p) (hx : p * x + x * p = x) :
    Matrix.trace x = 0 := by
  have h := (tangent_iff_odd_decomposition p x hp).mp hx
  calc
    Matrix.trace x = Matrix.trace (raise p x + lower p x) := congrArg Matrix.trace h
    _ = 0 := by rw [Matrix.trace_add, trace_raise p x hp, trace_lower p x hp]; simp

end InfoGeometry.Canonical.MatrixPeirceZorn.MatrixPeirce
