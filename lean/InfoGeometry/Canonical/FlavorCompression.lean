/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact loss certificates for real orthogonal frame compression

All norms in this file are Mathlib's Frobenius matrix norm. The response
matrix is arbitrary: the scaled-projector identity is an explicit hypothesis,
not an asserted octonion construction. The signed compression convention is
`Y = (T * L)ᵀ * R`, so its left Gram matrix is `Y * Yᵀ`.

The statements concern finite real matrices and global energy bounds. They
make no claim about stationary points, local minima, Hessian sufficiency,
octonion real forms, or physical flavor observables.
-/

noncomputable section

namespace InfoGeometry.Canonical.FlavorCompression

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {m n k p : Type*}
variable [Fintype m] [Fintype n] [Fintype k] [Fintype p]
variable [DecidableEq m] [DecidableEq n] [DecidableEq k] [DecidableEq p]

/-- The native Frobenius norm squared is the rectangular matrix Gram trace. -/
theorem frobenius_norm_sq_eq_trace (W : Matrix m n ℝ) :
    ‖W‖ ^ 2 = trace (Wᵀ * W) := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

/-- Either matrix Gram trace computes the same Frobenius energy. -/
theorem frobenius_norm_sq_eq_trace_mul_transpose (W : Matrix m n ℝ) :
    ‖W‖ ^ 2 = trace (W * Wᵀ) :=
  (frobenius_norm_sq_eq_trace W).trans (Matrix.trace_mul_comm Wᵀ W)

/-- Compressing by a symmetric idempotent retains its ordered Gram sandwich. -/
theorem projection_gram (P : Matrix m m ℝ) (hPs : Pᵀ = P) (hP : P * P = P)
    (W : Matrix m k ℝ) :
    (P * W)ᵀ * (P * W) = Wᵀ * P * W := by
  rw [Matrix.transpose_mul, hPs]
  calc
    (Wᵀ * P) * (P * W) = (Wᵀ * (P * P)) * W := by
      simp only [Matrix.mul_assoc]
    _ = Wᵀ * P * W := by rw [hP]

/-- The full Gram matrix splits into its orthogonal projection and residual. -/
theorem projection_gram_decomposition
    (P : Matrix m m ℝ) (hPs : Pᵀ = P) (hP : P * P = P)
    (W : Matrix m k ℝ) :
    Wᵀ * W = (P * W)ᵀ * (P * W) + ((1 - P) * W)ᵀ * ((1 - P) * W) := by
  have hQs : (1 - P)ᵀ = 1 - P := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, hPs]
  have hQ : (1 - P) * (1 - P) = 1 - P :=
    (show IsIdempotentElem P from hP).one_sub
  rw [projection_gram P hPs hP, projection_gram (1 - P) hQs hQ]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

/-- An orthonormal column frame determines an idempotent range projection. -/
theorem frame_projection_idempotent (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) :
    (R * Rᵀ) * (R * Rᵀ) = R * Rᵀ := by
  calc
    (R * Rᵀ) * (R * Rᵀ) = R * (Rᵀ * R) * Rᵀ := by
      simp only [Matrix.mul_assoc]
    _ = R * Rᵀ := by rw [hR, Matrix.mul_one]

/-- Exact matrix-valued loss identity for orthonormal frame compression. -/
theorem compression_gram_decomposition
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) (W : Matrix m k ℝ) :
    Wᵀ * W = (Wᵀ * R) * (Wᵀ * R)ᵀ +
      ((1 - R * Rᵀ) * W)ᵀ * ((1 - R * Rᵀ) * W) := by
  have hPs : (R * Rᵀ)ᵀ = R * Rᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP := frame_projection_idempotent R hR
  calc
    Wᵀ * W = ((R * Rᵀ) * W)ᵀ * ((R * Rᵀ) * W) +
        ((1 - R * Rᵀ) * W)ᵀ * ((1 - R * Rᵀ) * W) :=
      projection_gram_decomposition (R * Rᵀ) hPs hP W
    _ = (Wᵀ * R) * (Wᵀ * R)ᵀ +
        ((1 - R * Rᵀ) * W)ᵀ * ((1 - R * Rᵀ) * W) := by
      rw [projection_gram (R * Rᵀ) hPs hP]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Frobenius Pythagoras with the actual orthogonal-compression residual. -/
theorem compression_norm_sq_decomposition
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) (W : Matrix m k ℝ) :
    ‖W‖ ^ 2 = ‖Wᵀ * R‖ ^ 2 + ‖(1 - R * Rᵀ) * W‖ ^ 2 := by
  have h := congrArg Matrix.trace (compression_gram_decomposition R hR W)
  rw [Matrix.trace_add, ← frobenius_norm_sq_eq_trace W,
    ← frobenius_norm_sq_eq_trace_mul_transpose (Wᵀ * R),
    ← frobenius_norm_sq_eq_trace ((1 - R * Rᵀ) * W)] at h
  exact h

/-- Compression loss is exactly the squared norm of the discarded component. -/
theorem compression_loss
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) (W : Matrix m k ℝ) :
    ‖W‖ ^ 2 - ‖Wᵀ * R‖ ^ 2 = ‖(1 - R * Rᵀ) * W‖ ^ 2 := by
  rw [compression_norm_sq_decomposition R hR W, add_sub_cancel_left]

theorem compression_norm_sq_le
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) (W : Matrix m k ℝ) :
    ‖Wᵀ * R‖ ^ 2 ≤ ‖W‖ ^ 2 := by
  apply sub_nonneg.mp
  rw [compression_loss R hR W]
  exact sq_nonneg ‖(1 - R * Rᵀ) * W‖

/-- Equality of compression energies means that no matrix component is discarded. -/
theorem compression_norm_sq_eq_iff
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) (W : Matrix m k ℝ) :
    ‖Wᵀ * R‖ ^ 2 = ‖W‖ ^ 2 ↔ (1 - R * Rᵀ) * W = 0 := by
  have h := compression_loss R hR W
  constructor
  · intro heq
    have hz : ‖(1 - R * Rᵀ) * W‖ ^ 2 = 0 :=
      h.symm.trans (sub_eq_zero.mpr heq.symm)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro hz
    simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (sub_eq_zero.mp h).symm

/-- The response Gram identity is transported through an arbitrary left frame. -/
theorem scaled_response_gram
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C) (L : Matrix n k ℝ) :
    (T * L)ᵀ * (T * L) = c ^ 2 • (Lᵀ * C * L) := by
  rw [Matrix.transpose_mul]
  calc
    (Lᵀ * Tᵀ) * (T * L) = Lᵀ * (Tᵀ * T) * L := by
      simp only [Matrix.mul_assoc]
    _ = c ^ 2 • (Lᵀ * C * L) := by
      rw [hT, Matrix.mul_smul, Matrix.smul_mul]

theorem scaled_response_norm_sq
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C) (L : Matrix n k ℝ) :
    ‖T * L‖ ^ 2 = c ^ 2 * trace (Lᵀ * C * L) := by
  rw [frobenius_norm_sq_eq_trace, scaled_response_gram T C c hT L,
    Matrix.trace_smul, smul_eq_mul]

/-- An orthonormal frame's energy outside an orthogonal projector. -/
theorem frame_complement_norm_sq
    (C : Matrix n n ℝ) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1) :
    ‖(1 - C) * L‖ ^ 2 = (Fintype.card k : ℝ) - trace (Lᵀ * C * L) := by
  have hQs : (1 - C)ᵀ = 1 - C := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, hCs]
  have hQ : (1 - C) * (1 - C) = 1 - C :=
    (show IsIdempotentElem C from hC).one_sub
  rw [frobenius_norm_sq_eq_trace, projection_gram (1 - C) hQs hQ,
    Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub,
    hL, Matrix.trace_one]

/-- Exact conditional loss certificate for a response with scaled-projector Gram. -/
theorem scaled_compression_loss
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) :
    c ^ 2 * (Fintype.card k : ℝ) - ‖(T * L)ᵀ * R‖ ^ 2 =
      c ^ 2 * ‖(1 - C) * L‖ ^ 2 + ‖(1 - R * Rᵀ) * (T * L)‖ ^ 2 := by
  rw [← compression_loss R hR (T * L), scaled_response_norm_sq T C c hT L,
    frame_complement_norm_sq C hCs hC L hL]
  rw [mul_sub, sub_add_sub_cancel]

/-- The global compression bound follows from the two explicit nonnegative losses. -/
theorem scaled_compression_norm_sq_le
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) :
    ‖(T * L)ᵀ * R‖ ^ 2 ≤ c ^ 2 * (Fintype.card k : ℝ) := by
  apply sub_nonneg.mp
  rw [scaled_compression_loss T C c hT hCs hC L hL R hR]
  exact add_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg ‖(1 - C) * L‖))
    (sq_nonneg ‖(1 - R * Rᵀ) * (T * L)‖)

/-- At nonzero scale, global bound saturation is exactly vanishing of both losses. -/
theorem scaled_compression_saturation_iff
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ) (hc : c ≠ 0)
    (hT : Tᵀ * T = c ^ 2 • C) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1) :
    ‖(T * L)ᵀ * R‖ ^ 2 = c ^ 2 * (Fintype.card k : ℝ) ↔
      (1 - C) * L = 0 ∧ (1 - R * Rᵀ) * (T * L) = 0 := by
  have h := scaled_compression_loss T C c hT hCs hC L hL R hR
  constructor
  · intro heq
    have hA := mul_nonneg (sq_nonneg c) (sq_nonneg ‖(1 - C) * L‖)
    have hR' := sq_nonneg ‖(1 - R * Rᵀ) * (T * L)‖
    have hsum : c ^ 2 * ‖(1 - C) * L‖ ^ 2 +
        ‖(1 - R * Rᵀ) * (T * L)‖ ^ 2 = 0 :=
      h.symm.trans (sub_eq_zero.mpr heq.symm)
    obtain ⟨hA0, hR0⟩ := (add_eq_zero_iff_of_nonneg hA hR').mp hsum
    have hL0 : ‖(1 - C) * L‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hA0).resolve_left (pow_ne_zero 2 hc)
    exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hL0),
      norm_eq_zero.mp (sq_eq_zero_iff.mp hR0)⟩
  · rintro ⟨hA0, hR0⟩
    simp only [hA0, hR0, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, add_zero] at h
    exact (sub_eq_zero.mp h).symm

/-- Vanishing residuals force the full compressed Gram matrix to be scalar.
This is a conditional matrix identity, not a classification of local minima. -/
theorem compressed_gram_of_residuals_zero
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1)
    (hA0 : (1 - C) * L = 0) (hR0 : (1 - R * Rᵀ) * (T * L) = 0) :
    ((T * L)ᵀ * R) * ((T * L)ᵀ * R)ᵀ = c ^ 2 • (1 : Matrix k k ℝ) := by
  have hCL : C * L = L := by
    have h : L - C * L = 0 := by
      simpa only [Matrix.sub_mul, Matrix.one_mul] using hA0
    exact (sub_eq_zero.mp h).symm
  have hgram := compression_gram_decomposition R hR (T * L)
  simp only [hR0, Matrix.transpose_zero, Matrix.zero_mul, add_zero] at hgram
  rw [← hgram, scaled_response_gram T C c hT L, Matrix.mul_assoc, hCL, hL]

/-- Saturation forces a scalar left Gram at every scale, including zero.
At zero scale the readout itself vanishes; no vanishing left residual is inferred. -/
theorem compressed_gram_of_saturation
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1)
    (R : Matrix m p ℝ) (hR : Rᵀ * R = 1)
    (hsat : ‖(T * L)ᵀ * R‖ ^ 2 = c ^ 2 * (Fintype.card k : ℝ)) :
    ((T * L)ᵀ * R) * ((T * L)ᵀ * R)ᵀ = c ^ 2 • (1 : Matrix k k ℝ) := by
  by_cases hc : c = 0
  · have hnorm : ‖(T * L)ᵀ * R‖ ^ 2 = 0 := by simpa [hc] using hsat
    have hzero : (T * L)ᵀ * R = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    simp [hc, hzero]
  · obtain ⟨hA0, hR0⟩ :=
      (scaled_compression_saturation_iff T C c hc hT hCs hC L hL R hR).mp hsat
    exact compressed_gram_of_residuals_zero T C c hT L hL R hR hA0 hR0

/-- The exact two-sector certificate shares one left-frame loss. -/
theorem two_sector_scaled_compression_loss
    (T : Matrix m n ℝ) (C : Matrix n n ℝ) (c : ℝ)
    (hT : Tᵀ * T = c ^ 2 • C) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n k ℝ) (hL : Lᵀ * L = 1)
    (R₁ R₂ : Matrix m p ℝ) (hR₁ : R₁ᵀ * R₁ = 1) (hR₂ : R₂ᵀ * R₂ = 1) :
    2 * c ^ 2 * (Fintype.card k : ℝ) -
        (‖(T * L)ᵀ * R₁‖ ^ 2 + ‖(T * L)ᵀ * R₂‖ ^ 2) =
      2 * c ^ 2 * ‖(1 - C) * L‖ ^ 2 +
        ‖(1 - R₁ * R₁ᵀ) * (T * L)‖ ^ 2 +
        ‖(1 - R₂ * R₂ᵀ) * (T * L)‖ ^ 2 := by
  have h₁ := scaled_compression_loss T C c hT hCs hC L hL R₁ hR₁
  have h₂ := scaled_compression_loss T C c hT hCs hC L hL R₂ hR₂
  calc
    2 * c ^ 2 * (Fintype.card k : ℝ) -
        (‖(T * L)ᵀ * R₁‖ ^ 2 + ‖(T * L)ᵀ * R₂‖ ^ 2) =
      (c ^ 2 * (Fintype.card k : ℝ) - ‖(T * L)ᵀ * R₁‖ ^ 2) +
        (c ^ 2 * (Fintype.card k : ℝ) - ‖(T * L)ᵀ * R₂‖ ^ 2) := by
          rw [mul_assoc, two_mul, add_sub_add_comm]
    _ = (c ^ 2 * ‖(1 - C) * L‖ ^ 2 +
        ‖(1 - R₁ * R₁ᵀ) * (T * L)‖ ^ 2) +
      (c ^ 2 * ‖(1 - C) * L‖ ^ 2 +
        ‖(1 - R₂ * R₂ᵀ) * (T * L)‖ ^ 2) :=
      congrArg₂ (· + ·) h₁ h₂
    _ = 2 * c ^ 2 * ‖(1 - C) * L‖ ^ 2 +
        ‖(1 - R₁ * R₁ᵀ) * (T * L)‖ ^ 2 +
        ‖(1 - R₂ * R₂ᵀ) * (T * L)‖ ^ 2 := by
          rw [add_add_add_comm, ← two_mul, ← mul_assoc, add_assoc]

/-- With three columns and scale two, the two-sector global upper bound is 24. -/
theorem two_sector_three_frame_bound
    (T : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hT : Tᵀ * T = (2 : ℝ) ^ 2 • C) (hCs : Cᵀ = C) (hC : C * C = C)
    (L : Matrix n (Fin 3) ℝ) (hL : Lᵀ * L = 1)
    (R₁ R₂ : Matrix m p ℝ) (hR₁ : R₁ᵀ * R₁ = 1) (hR₂ : R₂ᵀ * R₂ = 1) :
    ‖(T * L)ᵀ * R₁‖ ^ 2 + ‖(T * L)ᵀ * R₂‖ ^ 2 ≤ 24 := by
  have h₁ := scaled_compression_norm_sq_le T C 2 hT hCs hC L hL R₁ hR₁
  have h₂ := scaled_compression_norm_sq_le T C 2 hT hCs hC L hL R₂ hR₂
  calc
    ‖(T * L)ᵀ * R₁‖ ^ 2 + ‖(T * L)ᵀ * R₂‖ ^ 2 ≤
        (2 : ℝ) ^ 2 * (Fintype.card (Fin 3) : ℝ) +
          (2 : ℝ) ^ 2 * (Fintype.card (Fin 3) : ℝ) :=
      add_le_add h₁ h₂
    _ = 24 := by norm_num

end InfoGeometry.Canonical.FlavorCompression
