/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeCutoffNative

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeCutoffFiniteEuler

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

open InfoGeometry.Arithmetic.PrimeCutoffNative

section DivisionRingCutoff

variable {D : Type*} [DivisionRing D]

/-- Modewise boson × signed Euler factor cancellation on `PrimeCutoff M` over any `[DivisionRing D]`. -/
theorem divisionRing_boson_mul_signed_factor
    (M : ℕ) (x : PrimeCutoff M → D) (p : PrimeCutoff M)
    (hp : 1 - x p ≠ 0) :
    (1 - x p)⁻¹ * (1 - x p) = 1 :=
  inv_mul_cancel₀ hp

/-- Modewise signed × boson Euler factor cancellation on `PrimeCutoff M` over any `[DivisionRing D]`. -/
theorem divisionRing_signed_mul_boson_factor
    (M : ℕ) (x : PrimeCutoff M → D) (p : PrimeCutoff M)
    (hp : 1 - x p ≠ 0) :
    (1 - x p) * (1 - x p)⁻¹ = 1 :=
  mul_inv_cancel₀ hp

/-- Modewise boson × square-signed = positive Euler factor on `PrimeCutoff M` over any `[DivisionRing D]`. -/
theorem divisionRing_boson_mul_square_signed_factor
    (M : ℕ) (x : PrimeCutoff M → D) (p : PrimeCutoff M)
    (hp : 1 - x p ≠ 0) :
    (1 - x p)⁻¹ * (1 - x p * x p) = 1 + x p := by
  have hsq : 1 - x p * x p = (1 - x p) * (1 + x p) := by noncomm_ring
  rw [hsq, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

end DivisionRingCutoff

theorem boson_mul_signed_cancel
    {R : Type*} [Field R] (M : ℕ)
    (x : PrimeCutoff M → R)
    (h : ∀ p, 1 - x p ≠ 0) :
    (∏ p : PrimeCutoff M, (1 - x p)⁻¹) *
        ∏ p : PrimeCutoff M, (1 - x p) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_eq_one
  intro p
  exact inv_mul_cancel₀ (h p)

theorem signed_cancel_boson
    {R : Type*} [Field R] (M : ℕ)
    (x : PrimeCutoff M → R)
    (h : ∀ p, 1 - x p ≠ 0) :
    (∏ p : PrimeCutoff M, (1 - x p)) *
        ∏ p : PrimeCutoff M, (1 - x p)⁻¹ = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_eq_one
  intro p
  exact mul_inv_cancel₀ (h p)

theorem boson_mul_square_signed_eq_positive
    {R : Type*} [Field R] (M : ℕ)
    (x : PrimeCutoff M → R)
    (h : ∀ p, 1 - x p ≠ 0) :
    (∏ p : PrimeCutoff M, (1 - x p)⁻¹) *
        ∏ p : PrimeCutoff M, (1 - x p * x p) =
      ∏ p : PrimeCutoff M, (1 + x p) := by
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro p
  calc
    (1 - x p)⁻¹ * (1 - x p * x p) =
        (1 - x p)⁻¹ * ((1 - x p) * (1 + x p)) := by ring
    _ = ((1 - x p)⁻¹ * (1 - x p)) * (1 + x p) := by ring
    _ = 1 * (1 + x p) := by rw [inv_mul_cancel₀ (h p)]
    _ = 1 + x p := by ring

end InfoGeometry.Arithmetic.PrimeCutoffFiniteEuler
