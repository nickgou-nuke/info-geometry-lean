/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Inner-derivation divergence, curl and finite boundary balance

The fields are full matrix-valued operators. Coordinate curl of an inner
gradient has a curvature defect; it is not automatically zero. Finite trace
kills global inner divergence, while compression by a noncentral projector
exposes an exact boundary flux. This does not invent a charge at infinity.
-/

namespace InfoGeometry.OperatorAlgebra.InnerDivergenceCharge

open Matrix
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section Algebra
variable {A ι : Type*} [Ring A]

def innerGradient (H : ι → A) (a : A) : ι → A := fun i => ⁅H i, a⁆

def innerCurl (H F : ι → A) (i j : ι) : A := ⁅H i, F j⁆ - ⁅H j, F i⁆

/-- Noncommuting frame directions leave an exact, nonzero-possible defect. -/
theorem curl_gradient_defect (H : ι → A) (a : A) (i j : ι) :
    innerCurl H (innerGradient H a) i j = ⁅⁅H i, H j⁆, a⁆ := by
  simp only [innerCurl, innerGradient, Ring.lie_def]
  noncomm_ring

theorem curl_gradient_zero_of_commute (H : ι → A) (a : A) (i j : ι)
    (hij : Commute (H i) (H j)) :
    innerCurl H (innerGradient H a) i j = 0 := by
  rw [curl_gradient_defect]
  simp [Ring.lie_def, hij.eq]

variable [Fintype ι]

def innerDivergence (H F : ι → A) : A := ∑ i, ⁅H i, F i⁆

end Algebra

section Trace
variable {R n ι : Type*} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The native trace evaluated on a genuine matrix commutator. -/
theorem trace_commutator (A B : Matrix n n R) : Matrix.trace ⁅A, B⁆ = 0 := by
  rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

theorem trace_innerDivergence (H F : ι → Matrix n n R) :
    Matrix.trace (innerDivergence H F) = 0 := by
  simp [innerDivergence, Matrix.trace_sum, trace_commutator]

theorem source_trace_necessary (H F : ι → Matrix n n R) (Q : Matrix n n R)
    (hQ : innerDivergence H F = Q) : Matrix.trace Q = 0 := by
  rw [← hQ, trace_innerDivergence]

/-- Matrix integration by parts, with no commutativity of the matrices. -/
theorem trace_integration_by_parts (H A B : Matrix n n R) :
    Matrix.trace (⁅H, A⁆ * B) = -Matrix.trace (A * ⁅H, B⁆) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, Matrix.trace_sub]
  have h : Matrix.trace ((H * A) * B) = Matrix.trace ((A * B) * H) := by
    rw [mul_assoc, Matrix.trace_mul_comm H (A * B)]
  rw [h]
  simp only [mul_assoc]
  abel

/-- Compression converts global divergence into a commutator boundary flux. -/
theorem compressed_trace_commutator (P H F : Matrix n n R) :
    Matrix.trace (P * ⁅H, F⁆) = Matrix.trace (⁅P, H⁆ * F) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, Matrix.trace_sub]
  have h : Matrix.trace (P * (F * H)) = Matrix.trace ((H * P) * F) := by
    rw [← mul_assoc, Matrix.trace_mul_comm (P * F) H, mul_assoc]
  rw [h, ← mul_assoc]

theorem compressed_divergence_flux (P : Matrix n n R) (H F : ι → Matrix n n R) :
    Matrix.trace (P * innerDivergence H F) =
      ∑ i, Matrix.trace (⁅P, H i⁆ * F i) := by
  simp [innerDivergence, Finset.mul_sum, Matrix.trace_sum, compressed_trace_commutator]

/-- The complementary region carries the opposite total finite trace flux. -/
theorem complementary_charge_balance (P : Matrix n n R) (H F : ι → Matrix n n R) :
    Matrix.trace (P * innerDivergence H F) +
      Matrix.trace ((1 - P) * innerDivergence H F) = 0 := by
  rw [← Matrix.trace_add, ← add_mul]
  simp [trace_innerDivergence]

/-- Finite weighted twisted cyclicity; not a full analytic KMS assertion. -/
theorem weighted_twisted_cyclicity (ρ : (Matrix n n R)ˣ) (A B : Matrix n n R) :
    Matrix.trace ((↑ρ : Matrix n n R) * (A * B)) =
      Matrix.trace (B * (↑ρ : Matrix n n R) * A) := by
  calc Matrix.trace ((↑ρ : Matrix n n R) * (A * B))
      = Matrix.trace (((↑ρ : Matrix n n R) * A) * B) := by rw [mul_assoc]
    _ = Matrix.trace (B * ((↑ρ : Matrix n n R) * A)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * (↑ρ : Matrix n n R) * A) := by rw [mul_assoc]

end Trace

section PositiveSource
variable {m n ι : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- Faithfulness of the concrete rectangular real Gramian trace. -/
theorem eq_zero_of_trace_gramian_zero (B : Matrix m n ℝ)
    (hB : Matrix.trace (Bᵀ * B) = 0) : B = 0 := by
  have hs : (∑ j, ∑ i, B i j * B i j) = 0 := by
    simpa [Matrix.trace, Matrix.mul_apply] using hB
  have hn (j : n) : 0 ≤ ∑ i, B i j * B i j :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (B i j))
  ext i j
  have hj : (∑ k, B k j * B k j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).mp hs j (Finset.mem_univ j)
  have hi : B i j * B i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (B k j))).mp
      hj i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hi

/-- No nonzero positive Gramian can be a boundary-free finite inner divergence. -/
theorem nonzero_gramian_not_divergence (B : Matrix m n ℝ) (hB : B ≠ 0)
    (H F : ι → Matrix n n ℝ) : innerDivergence H F ≠ Bᵀ * B := by
  intro h
  exact hB (eq_zero_of_trace_gramian_zero B (source_trace_necessary H F _ h))

end PositiveSource

end InfoGeometry.OperatorAlgebra.InnerDivergenceCharge
