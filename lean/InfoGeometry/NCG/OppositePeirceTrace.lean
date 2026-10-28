/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.OppositePeirceCoupling
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-! # Trace and positivity of opposite Peirce coupling

Trace identities use commutative coefficients, not commuting matrices.
Positivity and nonvanishing are proved separately for a complex adjoint pair.
-/

namespace InfoGeometry.NCG.OppositePeirceTrace

open Matrix NonCommutativeFredholmIndex
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open InfoGeometry.NCG.OppositePeirceCoupling

variable {n : Type*} [Fintype n] [DecidableEq n]

section Trace
variable {R : Type*} [CommRing R] {P : Matrix n n R}

theorem trace_component10 (hP : IsIdempotentElem P) (A : Matrix n n R) :
    trace (component10 P A) = 0 := by
  change trace ((P * A) * (1 - P)) = 0
  rw [trace_mul_comm, ← mul_assoc, hP.one_sub_mul_self, zero_mul, trace_zero]

theorem trace_component01 (hP : IsIdempotentElem P) (B : Matrix n n R) :
    trace (component01 P B) = 0 := by
  change trace (((1 - P) * B) * P) = 0
  rw [trace_mul_comm, ← mul_assoc, hP.mul_one_sub_self, zero_mul, trace_zero]

theorem trace_sum_sq (hP : IsIdempotentElem P) (A B : Matrix n n R) :
    trace ((component10 P A + component01 P B) *
      (component10 P A + component01 P B)) =
      2 • trace (component10 P A * component01 P B) := by
  rw [sum_sq hP A B, anticommutator, trace_add,
    trace_mul_comm (component01 P B), two_nsmul]

theorem trace_reflection_mul_commutator (hP : IsIdempotentElem P) (A B : Matrix n n R) :
    trace (reflection P * commutator (component10 P A) (component01 P B)) =
      2 • trace (component10 P A * component01 P B) := by
  rw [← anticommutator_eq_reflection_mul hP A B, anticommutator, trace_add,
    trace_mul_comm (component01 P B), two_nsmul]

theorem trace_anticommutator_corners (hP : IsIdempotentElem P) (A B : Matrix n n R) :
    trace (component11 P (anticommutator (component10 P A) (component01 P B))) =
      trace (component00 P (anticommutator (component10 P A) (component01 P B))) := by
  rw [component11_anticommutator hP A B, component00_anticommutator hP A B]
  exact trace_mul_comm _ _

theorem trace_commutator_corners_add (hP : IsIdempotentElem P) (A B : Matrix n n R) :
    trace (component11 P (commutator (component10 P A) (component01 P B))) +
      trace (component00 P (commutator (component10 P A) (component01 P B))) = 0 := by
  rw [component11_commutator hP A B, component00_commutator hP A B,
    trace_neg, trace_mul_comm (component01 P B), add_neg_cancel]

end Trace

section Star
variable {R : Type*} [Ring R] [StarRing R] {P : Matrix n n R}

/-- The reverse corner of the adjoint is the adjoint of the forward corner. -/
theorem component01_conjTranspose (hP : P.IsHermitian) (A : Matrix n n R) :
    component01 P Aᴴ = (component10 P A)ᴴ := by
  simp only [component01, component10, complementIdempotent, conjTranspose_mul,
    conjTranspose_sub, conjTranspose_one, hP.eq, mul_assoc]

theorem adjoint_sum_isHermitian (hP : P.IsHermitian) (A : Matrix n n R) :
    (component10 P A + component01 P Aᴴ).IsHermitian := by
  rw [component01_conjTranspose hP A]
  change (component10 P A + (component10 P A)ᴴ)ᴴ = _
  rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]

end Star

section Positive
open scoped ComplexOrder
variable {P : Matrix n n ℂ}

theorem adjoint_anticommutator_posSemidef (hP : P.IsHermitian) (A : Matrix n n ℂ) :
    (anticommutator (component10 P A) (component01 P Aᴴ)).PosSemidef := by
  rw [component01_conjTranspose hP A, anticommutator]
  exact (posSemidef_self_mul_conjTranspose _).add (posSemidef_conjTranspose_mul_self _)

theorem adjoint_sum_sq_posSemidef (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℂ) :
    ((component10 P A + component01 P Aᴴ) *
      (component10 P A + component01 P Aᴴ)).PosSemidef := by
  rw [sum_sq hP A Aᴴ]
  exact adjoint_anticommutator_posSemidef hPs A

/-- Nonnegativity uses mathlib's explicit complex partial order. -/
theorem trace_adjoint_anticommutator_nonneg (hP : P.IsHermitian) (A : Matrix n n ℂ) :
    0 ≤ trace (anticommutator (component10 P A) (component01 P Aᴴ)) := by
  exact Finset.sum_nonneg fun i _ => (adjoint_anticommutator_posSemidef hP A).diag_nonneg

/-- Faithfulness requires the adjoint pair; it is false for independent corners. -/
theorem adjoint_anticommutator_eq_zero_iff (hP : IsIdempotentElem P)
    (hPs : P.IsHermitian) (A : Matrix n n ℂ) :
    anticommutator (component10 P A) (component01 P Aᴴ) = 0 ↔ component10 P A = 0 := by
  constructor
  · intro h
    have hx := ((anticommutator_eq_zero_iff_products hP A Aᴴ).mp h).1
    rw [component01_conjTranspose hPs A] at hx
    exact trace_mul_conjTranspose_self_eq_zero_iff.mp (by rw [hx, trace_zero])
  · intro h
    simp [anticommutator, h]

theorem adjoint_commutator_ne_zero_iff (hP : IsIdempotentElem P)
    (hPs : P.IsHermitian) (A : Matrix n n ℂ) :
    commutator (component10 P A) (component01 P Aᴴ) ≠ 0 ↔ component10 P A ≠ 0 := by
  exact not_congr ((anticommutator_eq_zero_iff_commutator hP A Aᴴ).symm.trans
    (adjoint_anticommutator_eq_zero_iff hP hPs A))

theorem adjoint_sum_sq_eq_zero_iff (hP : IsIdempotentElem P)
    (hPs : P.IsHermitian) (A : Matrix n n ℂ) :
    (component10 P A + component01 P Aᴴ) *
      (component10 P A + component01 P Aᴴ) = 0 ↔ component10 P A = 0 := by
  rw [sum_sq hP A Aᴴ, adjoint_anticommutator_eq_zero_iff hP hPs A]

end Positive
end InfoGeometry.NCG.OppositePeirceTrace
