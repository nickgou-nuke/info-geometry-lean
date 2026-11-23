/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Associative Peirce four-block decomposition

For an associative unital ring `A` and an idempotent `f : A`, put
`e = 1 - f`.  Then `e` is idempotent, `f * e = e * f = 0`, and every
`x : A` admits the canonical four-block expansion

`x = f*x*f + f*x*e + e*x*f + e*x*e`.

The four Peirce sectors are represented elementwise as

* `A₁₁ = f A f`,
* `A₁₀ = f A e`,
* `A₀₁ = e A f`,
* `A₀₀ = e A e`.

This file proves the complete associative routing table
`Aᵢⱼ Aₖₗ ⊆ Aᵢₗ` when `j = k`, and zero multiplication when `j ≠ k`.
No Jordan-specific Peirce eigenvalue claims are made here.
-/

namespace InfoGeometry.Core.PeirceDecomposition

section AssociativePeirce

variable {A : Type*} [Ring A]

/-- The complementary idempotent candidate `1 - f`. -/
def complementIdempotent (f : A) : A :=
  1 - f

@[simp]
theorem add_complementIdempotent (f : A) :
    f + complementIdempotent f = 1 := by
  simp [complementIdempotent]

@[simp]
theorem complementIdempotent_add (f : A) :
    complementIdempotent f + f = 1 := by
  simp [complementIdempotent]

/-- The complement of an idempotent is idempotent. -/
@[simp]
theorem complementIdempotent_sq
    (f : A) (hf : f * f = f) :
    complementIdempotent f * complementIdempotent f =
      complementIdempotent f := by
  simp [complementIdempotent, mul_sub, sub_mul, hf]

/-- An idempotent is left-orthogonal to its complement. -/
@[simp]
theorem idempotent_mul_complement
    (f : A) (hf : f * f = f) :
    f * complementIdempotent f = 0 := by
  simp [complementIdempotent, mul_sub, hf]

/-- An idempotent is right-orthogonal to its complement. -/
@[simp]
theorem complement_mul_idempotent
    (f : A) (hf : f * f = f) :
    complementIdempotent f * f = 0 := by
  simp [complementIdempotent, sub_mul, hf]

@[simp] theorem idempotent_mul_nested
    (f : A) (hf : f * f = f) (x : A) :
    f * (f * x) = f * x := by
  rw [← mul_assoc, hf]

@[simp] theorem complement_mul_nested
    (f : A) (hf : f * f = f) (x : A) :
    complementIdempotent f * (complementIdempotent f * x) =
      complementIdempotent f * x := by
  rw [← mul_assoc, complementIdempotent_sq f hf]

@[simp] theorem idempotent_complement_nested
    (f : A) (hf : f * f = f) (x : A) :
    f * (complementIdempotent f * x) = 0 := by
  rw [← mul_assoc, idempotent_mul_complement f hf, zero_mul]

@[simp] theorem complement_idempotent_nested
    (f : A) (hf : f * f = f) (x : A) :
    complementIdempotent f * (f * x) = 0 := by
  rw [← mul_assoc, complement_mul_idempotent f hf, zero_mul]

theorem peirce_cross_zero
    {u v a b : A} (huv : u * v = 0) :
    a * (u * (v * b)) = 0 := by
  calc
    a * (u * (v * b)) = a * ((u * v) * b) := by
      rw [mul_assoc]
    _ = 0 := by rw [huv, zero_mul, mul_zero]

/-- The `11` Peirce sector `f A f`. -/
def peirce11 (f : A) : Set A :=
  {x | ∃ a : A, x = f * a * f}

/-- The `10` Peirce sector `f A (1-f)`. -/
def peirce10 (f : A) : Set A :=
  {x | ∃ a : A, x = f * a * complementIdempotent f}

/-- The `01` Peirce sector `(1-f) A f`. -/
def peirce01 (f : A) : Set A :=
  {x | ∃ a : A, x = complementIdempotent f * a * f}

/-- The `00` Peirce sector `(1-f) A (1-f)`. -/
def peirce00 (f : A) : Set A :=
  {x | ∃ a : A,
    x = complementIdempotent f * a * complementIdempotent f}

/-- Canonical `11` component. -/
def component11 (f x : A) : A :=
  f * x * f

/-- Canonical `10` component. -/
def component10 (f x : A) : A :=
  f * x * complementIdempotent f

/-- Canonical `01` component. -/
def component01 (f x : A) : A :=
  complementIdempotent f * x * f

/-- Canonical `00` component. -/
def component00 (f x : A) : A :=
  complementIdempotent f * x * complementIdempotent f

/-- The commutator with a cut is the difference of its two directed Peirce
corners. The diagonal blocks cancel, so noncommutation is exactly an imbalance
between the two directions; it does not imply that both directions are nonzero. -/
theorem commutator_eq_component10_sub_component01 (f x : A) :
    f * x - x * f = component10 f x - component01 f x := by
  simp only [component10, component01, complementIdempotent]
  noncomm_ring

/-- A coefficient commutes with the cut precisely when its two directed
off-diagonal Peirce components agree. -/
theorem commutes_with_idempotent_iff_component10_eq_component01 (f x : A) :
    f * x = x * f ↔ component10 f x = component01 f x := by
  rw [← sub_eq_zero, commutator_eq_component10_sub_component01]
  exact sub_eq_zero

@[simp]
theorem component11_mem (f x : A) :
    component11 f x ∈ peirce11 f := by
  exact ⟨x, rfl⟩

@[simp]
theorem component10_mem (f x : A) :
    component10 f x ∈ peirce10 f := by
  exact ⟨x, rfl⟩

@[simp]
theorem component01_mem (f x : A) :
    component01 f x ∈ peirce01 f := by
  exact ⟨x, rfl⟩

@[simp]
theorem component00_mem (f x : A) :
    component00 f x ∈ peirce00 f := by
  exact ⟨x, rfl⟩

/-- Every element is the sum of its four associative Peirce blocks.

This identity is purely distributive and does not require idempotency. -/
theorem peirce_decomposition (f x : A) :
    x =
      component11 f x + component10 f x +
      component01 f x + component00 f x := by
  simp only [component11, component10, component01, component00,
    complementIdempotent]
  noncomm_ring

/-- The idempotency defect `x * x - x` resolves into the four ordered
Peirce corners.  The diagonal defects receive the two round-trip transfer
terms, while the off-diagonal components are the corresponding two-step
paths minus the original component. -/
theorem idempotencyDefect_peirce_components
    (f x : A) (hf : f * f = f) :
    component11 f (x * x - x) =
        (component11 f x * component11 f x - component11 f x) +
          component10 f x * component01 f x ∧
    component10 f (x * x - x) =
        component11 f x * component10 f x +
          component10 f x * component00 f x - component10 f x ∧
    component01 f (x * x - x) =
        component01 f x * component11 f x +
          component00 f x * component01 f x - component01 f x ∧
    component00 f (x * x - x) =
        (component00 f x * component00 f x - component00 f x) +
          component01 f x * component10 f x := by
  simp only [component11, component10, component01, component00,
    complementIdempotent]
  have hcomp : complementIdempotent f * complementIdempotent f = complementIdempotent f := by
    rw [complementIdempotent_sq f hf]
  constructor
  · noncomm_ring [hf, hcomp]
    simp only [idempotent_mul_nested f hf]
    abel_nf
  · noncomm_ring [hf, hcomp]
    simp only [idempotent_mul_nested f hf]
    abel_nf
    simp

/-- An element is idempotent exactly when each of its four Peirce defect
components vanishes. The diagonal conditions include the two ordered
off-diagonal round trips; in general these products are distinct. -/
theorem isIdempotent_iff_peirceDefect_components
    (f x : A) (hf : f * f = f) :
    x * x = x ↔
      ((component11 f x * component11 f x - component11 f x) +
          component10 f x * component01 f x = 0 ∧
        component11 f x * component10 f x +
          component10 f x * component00 f x - component10 f x = 0 ∧
        component01 f x * component11 f x +
          component00 f x * component01 f x - component01 f x = 0 ∧
        (component00 f x * component00 f x - component00 f x) +
          component01 f x * component10 f x = 0) := by
  constructor
  · intro hx
    have hparts := idempotencyDefect_peirce_components f x hf
    rw [hx] at hparts
    rcases hparts with ⟨h11, h10, h01, h00⟩
    exact ⟨by simpa [component11, component10, component01, component00] using h11.symm,
      by simpa [component11, component10, component01, component00] using h10.symm,
      by simpa [component11, component10, component01, component00] using h01.symm,
      by simpa [component11, component10, component01, component00] using h00.symm⟩
  · rintro ⟨h11, h10, h01, h00⟩
    have hparts := idempotencyDefect_peirce_components f x hf
    rcases hparts with ⟨h11', h10', h01', h00'⟩
    rw [h11] at h11'
    rw [h10] at h10'
    rw [h01] at h01'
    rw [h00] at h00'
    have hsum := peirce_decomposition f (x * x - x)
    rw [h11', h10', h01', h00'] at hsum
    simp at hsum
    exact sub_eq_zero.mp hsum

/-! ## Nonzero routing laws -/

/-- `A₁₁ A₁₁ ⊆ A₁₁`. -/
theorem peirce11_mul_peirce11
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce11 f) :
    x * y ∈ peirce11 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₁₁ A₁₀ ⊆ A₁₀`. -/
theorem peirce11_mul_peirce10
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce10 f) :
    x * y ∈ peirce10 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₁₀ A₀₁ ⊆ A₁₁`. -/
theorem peirce10_mul_peirce01
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce01 f) :
    x * y ∈ peirce11 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `A₁₀ A₀₀ ⊆ A₁₀`. -/
theorem peirce10_mul_peirce00
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce00 f) :
    x * y ∈ peirce10 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `A₀₁ A₁₁ ⊆ A₀₁`. -/
theorem peirce01_mul_peirce11
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce11 f) :
    x * y ∈ peirce01 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₀₁ A₁₀ ⊆ A₀₀`. -/
theorem peirce01_mul_peirce10
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce10 f) :
    x * y ∈ peirce00 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₀₀ A₀₁ ⊆ A₀₁`. -/
theorem peirce00_mul_peirce01
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce01 f) :
    x * y ∈ peirce01 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `A₀₀ A₀₀ ⊆ A₀₀`. -/
theorem peirce00_mul_peirce00
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce00 f) :
    x * y ∈ peirce00 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-! ## Zero routing laws -/

/-- `A₁₁ A₀₁ = 0`. -/
theorem peirce11_mul_peirce01_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce01 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := f) (v := complementIdempotent f)
      (a := f * a) (b := b * f) (idempotent_mul_complement f hf))

/-- `A₁₁ A₀₀ = 0`. -/
theorem peirce11_mul_peirce00_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce00 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := f) (v := complementIdempotent f)
      (a := f * a) (b := b * complementIdempotent f)
      (idempotent_mul_complement f hf))

/-- `A₁₀ A₁₁ = 0`. -/
theorem peirce10_mul_peirce11_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce11 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := complementIdempotent f) (v := f)
      (a := f * a) (b := b * f) (complement_mul_idempotent f hf))

/-- `A₁₀ A₁₀ = 0`. -/
theorem peirce10_mul_peirce10_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce10 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := complementIdempotent f) (v := f)
      (a := f * a) (b := b * complementIdempotent f)
      (complement_mul_idempotent f hf))

/-- `A₀₁ A₀₁ = 0`. -/
theorem peirce01_mul_peirce01_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce01 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := f) (v := complementIdempotent f)
      (a := complementIdempotent f * a) (b := b * f)
      (idempotent_mul_complement f hf))

/-- `A₀₁ A₀₀ = 0`. -/
theorem peirce01_mul_peirce00_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce00 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := f) (v := complementIdempotent f)
      (a := complementIdempotent f * a) (b := b * complementIdempotent f)
      (idempotent_mul_complement f hf))

/-- `A₀₀ A₁₁ = 0`. -/
theorem peirce00_mul_peirce11_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce11 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := complementIdempotent f) (v := f)
      (a := complementIdempotent f * a) (b := b * f)
      (complement_mul_idempotent f hf))

/-- `A₀₀ A₁₀ = 0`. -/
theorem peirce00_mul_peirce10_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce10 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simpa only [mul_assoc] using
    (peirce_cross_zero (A := A) (u := complementIdempotent f) (v := f)
      (a := complementIdempotent f * a) (b := b * complementIdempotent f)
      (complement_mul_idempotent f hf))

/-! ## Corner units -/

/-- `f` acts as a left identity on `A₁₁`. -/
theorem peirce11_absorb_left
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce11 f) :
    f * x = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, hf]

/-- `f` acts as a right identity on `A₁₁`. -/
theorem peirce11_absorb_right
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce11 f) :
    x * f = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, hf]

/-- `1-f` acts as a left identity on `A₀₀`. -/
theorem peirce00_absorb_left
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    complementIdempotent f * x = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `1-f` acts as a right identity on `A₀₀`. -/
theorem peirce00_absorb_right
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    x * complementIdempotent f = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- The two ordered round trips through opposite Peirce corners form a
block-diagonal sum, hence commute with the cut. -/
theorem opposite_corner_roundtrip_sum_commutes
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce01 f) :
    f * (x * y + y * x) = (x * y + y * x) * f := by
  have hxy : x * y ∈ peirce11 f := peirce10_mul_peirce01 f hf hx hy
  have hyx : y * x ∈ peirce00 f := peirce01_mul_peirce10 f hf hy hx
  have hleft : f * (y * x) = 0 := by
    have hq := peirce00_absorb_left f hf hyx
    calc
      f * (y * x) = f * (complementIdempotent f * (y * x)) :=
        congrArg (fun z => f * z) hq.symm
      _ = 0 := by rw [← mul_assoc, idempotent_mul_complement f hf, zero_mul]
  have hright : (y * x) * f = 0 := by
    have hq := peirce00_absorb_right f hf hyx
    calc
      (y * x) * f = ((y * x) * complementIdempotent f) * f :=
        congrArg (fun z => z * f) hq.symm
      _ = 0 := by rw [mul_assoc, complement_mul_idempotent f hf, mul_zero]
  calc
    f * (x * y + y * x) = x * y + 0 := by
      rw [mul_add, peirce11_absorb_left f hf hxy, hleft]
    _ = (x * y) * f + (y * x) * f := by
      rw [peirce11_absorb_right f hf hxy, hright]
    _ = (x * y + y * x) * f := (add_mul _ _ _).symm

/-- The ordered round-trip difference also lies in the diagonal Peirce
algebra and therefore commutes with the cut. -/
theorem opposite_corner_roundtrip_difference_commutes
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce01 f) :
    f * (y * x - x * y) = (y * x - x * y) * f := by
  have hxy : x * y ∈ peirce11 f := peirce10_mul_peirce01 f hf hx hy
  have hyx : y * x ∈ peirce00 f := peirce01_mul_peirce10 f hf hy hx
  have hleft : f * (y * x) = 0 := by
    have hq := peirce00_absorb_left f hf hyx
    calc
      f * (y * x) = f * (complementIdempotent f * (y * x)) :=
        congrArg (fun z => f * z) hq.symm
      _ = 0 := by rw [← mul_assoc, idempotent_mul_complement f hf, zero_mul]
  have hright : (y * x) * f = 0 := by
    have hq := peirce00_absorb_right f hf hyx
    calc
      (y * x) * f = ((y * x) * complementIdempotent f) * f :=
        congrArg (fun z => z * f) hq.symm
      _ = 0 := by rw [mul_assoc, complement_mul_idempotent f hf, mul_zero]
  calc
    f * (y * x - x * y) = 0 - x * y := by
      rw [mul_sub, hleft, peirce11_absorb_left f hf hxy]
    _ = (y * x) * f - (x * y) * f := by
      rw [peirce11_absorb_right f hf hxy, hright]
    _ = (y * x - x * y) * f := (sub_mul _ _ _).symm

/-- With the grading `f - (1-f)`, the directed commutator is the
negative graded anticommutator. This fixes the order-sensitive sign. -/
theorem opposite_corner_commutator_eq_neg_graded_roundtrip_sum
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce01 f) :
    y * x - x * y =
      -((f - complementIdempotent f) * (x * y + y * x)) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  let q := complementIdempotent f
  have hxy : (f * a * q) * (q * b * f) ∈ peirce11 f :=
    peirce10_mul_peirce01 f hf ⟨a, rfl⟩ ⟨b, rfl⟩
  have hyx : (q * b * f) * (f * a * q) ∈ peirce00 f :=
    peirce01_mul_peirce10 f hf ⟨b, rfl⟩ ⟨a, rfl⟩
  have hxyFix := peirce11_absorb_left f hf hxy
  have hyxFix := peirce00_absorb_left f hf hyx
  have hqxy : q * ((f * a * q) * (q * b * f)) = 0 := by
    calc
      q * ((f * a * q) * (q * b * f)) = q * (f * ((f * a * q) * (q * b * f))) :=
        congrArg (fun z => q * z) hxyFix.symm
      _ = 0 := by rw [← mul_assoc, complement_mul_idempotent f hf, zero_mul]
  have hfyx : f * ((q * b * f) * (f * a * q)) = 0 := by
    calc
      f * ((q * b * f) * (f * a * q)) = f * (q * ((q * b * f) * (f * a * q))) :=
        congrArg (fun z => f * z) hyxFix.symm
      _ = 0 := by rw [← mul_assoc, idempotent_mul_complement f hf, zero_mul]
  have hleft : (f - q) *
      ((f * a * q) * (q * b * f) + (q * b * f) * (f * a * q)) =
        (f * a * q) * (q * b * f) - (q * b * f) * (f * a * q) := by
    rw [sub_mul, mul_add, mul_add, hxyFix, hfyx, hqxy, hyxFix]
    abel
  change (q * b * f) * (f * a * q) - (f * a * q) * (q * b * f) =
    -((f - q) * ((f * a * q) * (q * b * f) + (q * b * f) * (f * a * q)))
  rw [hleft]
  abel

/-- For `X ∈ (1-f)Af` and `Y ∈ fA(1-f)`, the order used by the
graded operator convention gives `[Y,X] = (f-(1-f)){X,Y}`. -/
theorem peirce01_peirce10_commutator_eq_graded_roundtrip_sum
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce10 f) :
    y * x - x * y =
      (f - complementIdempotent f) * (x * y + y * x) := by
  have h := opposite_corner_commutator_eq_neg_graded_roundtrip_sum f hf hy hx
  calc
    y * x - x * y = -(x * y - y * x) := by noncomm_ring
    _ = -(-((f - complementIdempotent f) * (y * x + x * y))) := by rw [h]
    _ = (f - complementIdempotent f) * (x * y + y * x) := by
      rw [neg_neg, add_comm]

/-! ## Elementwise Peirce corners -/

/-- The `(p, q)`-Peirce corner `p * x * q`. -/
def peirceCorner (p q x : A) : A :=
  p * x * q

/-- A Peirce corner is square-zero when the right and left projectors are
orthogonal in the order `q * p = 0`. -/
theorem peirceCorner_sq_eq_zero {p q x : A} (h : q * p = 0) :
    peirceCorner p q x * peirceCorner p q x = 0 := by
  unfold peirceCorner
  calc
    (p * x * q) * (p * x * q) = p * x * (q * p) * x * q := by
      noncomm_ring
    _ = 0 := by rw [h, mul_zero, zero_mul, zero_mul]

/-- The `10` component of a cut is square-zero. -/
theorem component10_sq_eq_zero (f x : A) (hf : f * f = f) :
    component10 f x * component10 f x = 0 := by
  simpa [component10, peirceCorner, complementIdempotent] using
    (peirceCorner_sq_eq_zero (p := f) (q := complementIdempotent f) (x := x)
      (complement_mul_idempotent f hf))

/-- The `01` component of a cut is square-zero. -/
theorem component01_sq_eq_zero (f x : A) (hf : f * f = f) :
    component01 f x * component01 f x = 0 := by
  simpa [component01, peirceCorner, complementIdempotent] using
    (peirceCorner_sq_eq_zero (p := complementIdempotent f) (q := f) (x := x)
      (idempotent_mul_complement f hf))

/-- A Peirce corner is left-absorbed by its left idempotent. -/
theorem peirceCorner_absorb_left {p q x : A} (hp : p * p = p) :
    p * peirceCorner p q x = peirceCorner p q x := by
  unfold peirceCorner
  calc
    p * (p * x * q) = (p * p) * x * q := by noncomm_ring
    _ = p * x * q := by rw [hp]

/-- A Peirce corner is right-absorbed by its right idempotent. -/
theorem peirceCorner_absorb_right {p q x : A} (hq : q * q = q) :
    peirceCorner p q x * q = peirceCorner p q x := by
  unfold peirceCorner
  calc
    (p * x * q) * q = p * x * (q * q) := by noncomm_ring
    _ = p * x * q := by rw [hq]

end AssociativePeirce

end InfoGeometry.Core.PeirceDecomposition
