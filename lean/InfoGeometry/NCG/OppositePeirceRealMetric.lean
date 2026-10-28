/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.OppositePeirceTrace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith

/-!
# Real metric kernel and Krein-adjoint distinction

The positive adjoint is real transpose. Strict positivity is characterized by
an actual common kernel, not by nonzero coupling. Multiplication by the grading
produces a Krein-self-adjoint operator with the negative square, which is not
positive semidefinite unless the coupling vanishes. No new bracket or carrier.
-/

namespace InfoGeometry.NCG.OppositePeirceRealMetric

open Matrix NonCommutativeFredholmIndex
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading
open InfoGeometry.NCG.OppositePeirceCoupling InfoGeometry.NCG.OppositePeirceTrace

variable {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}

local notation "X" => component10 P
local notation "Y" => component01 P

/-- Left support extracts the first arrow without cancellation of two. -/
theorem left_support (hP : IsIdempotentElem P) (A B : Matrix n n ℝ) :
    P * (X A + Y B) = X A := by
  simp only [component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

theorem complement_left_support (hP : IsIdempotentElem P) (A B : Matrix n n ℝ) :
    (1 - P) * (X A + Y B) = Y B := by
  simp only [component10, component01, complementIdempotent]
  noncomm_ring [hP.eq, idempotent_mul_nested P hP.eq]

/-- Opposite supports prevent cancellation of the two vector images. -/
theorem sum_mulVec_zero_iff (hP : IsIdempotentElem P) (A B : Matrix n n ℝ)
    (x : n → ℝ) :
    (X A + Y B) *ᵥ x = 0 ↔ X A *ᵥ x = 0 ∧ Y B *ᵥ x = 0 := by
  constructor
  · intro hx
    constructor
    · rw [← left_support hP A B, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    · rw [← complement_left_support hP A B, ← Matrix.mulVec_mulVec, hx,
        Matrix.mulVec_zero]
  · rintro ⟨hu, hv⟩
    rw [Matrix.add_mulVec, hu, hv, add_zero]

/-- The ordinary trace is faithful for the real adjoint coupling. -/
theorem trace_square_zero_iff (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) :
    trace ((X A + Y Aᴴ) * (X A + Y Aᴴ)) = 0 ↔ X A = 0 := by
  rw [trace_sum_sq hP A Aᴴ, component01_conjTranspose hPs A, two_nsmul]
  have ht : trace (X A * (X A)ᴴ) = 0 ↔ X A = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff
  constructor
  · intro hz
    apply ht.mp
    linarith
  · intro hu
    rw [ht.mpr hu, add_zero]

theorem trace_square_pos_iff (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) :
    0 < trace ((X A + Y Aᴴ) * (X A + Y Aᴴ)) ↔ X A ≠ 0 := by
  have hn := (adjoint_sum_sq_posSemidef hP hPs A).trace_nonneg
  have hz := trace_square_zero_iff hP hPs A
  constructor
  · intro h hu
    have ht := hz.mpr hu
    linarith
  · intro hu
    have ht : trace ((X A + Y Aᴴ) * (X A + Y Aᴴ)) ≠ 0 := fun h => hu (hz.mp h)
    exact lt_of_le_of_ne hn (Ne.symm ht)

/-- The complete zero-mode condition, including singular nonzero couplings. -/
theorem square_mulVec_zero_iff (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) (x : n → ℝ) :
    ((X A + Y Aᴴ) * (X A + Y Aᴴ)) *ᵥ x = 0 ↔
      X A *ᵥ x = 0 ∧ (X A)ᴴ *ᵥ x = 0 := by
  have h := Matrix.conjTranspose_mul_self_mulVec_eq_zero (X A + Y Aᴴ) x
  rw [(adjoint_sum_isHermitian hPs A).eq] at h
  rw [h, ← component01_conjTranspose hPs A]
  exact sum_mulVec_zero_iff hP A Aᴴ x

/-- Equality of native kernel submodules, not a dimension-only readout. -/
theorem square_ker (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) :
    LinearMap.ker (Matrix.toLin' ((X A + Y Aᴴ) * (X A + Y Aᴴ))) =
      LinearMap.ker (Matrix.toLin' (X A)) ⊓ LinearMap.ker (Matrix.toLin' ((X A)ᴴ)) := by
  ext x
  change ((X A + Y Aᴴ) * (X A + Y Aᴴ)) *ᵥ x = 0 ↔
    X A *ᵥ x = 0 ∧ (X A)ᴴ *ᵥ x = 0
  exact square_mulVec_zero_iff hP hPs A x

/-- Nonzero coupling alone is insufficient for strict positive definiteness. -/
theorem square_posDef_iff (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) :
    ((X A + Y Aᴴ) * (X A + Y Aᴴ)).PosDef ↔
      ∀ x : n → ℝ, X A *ᵥ x = 0 → (X A)ᴴ *ᵥ x = 0 → x = 0 := by
  constructor
  · intro h x hu hv
    by_contra hx
    have hk := (square_mulVec_zero_iff hP hPs A x).mpr ⟨hu, hv⟩
    have hpos := h.dotProduct_mulVec_pos hx
    have : (0 : ℝ) < 0 := by simpa only [hk, dotProduct_zero] using hpos
    exact (lt_irrefl (0 : ℝ)) this
  · intro hker
    have hps := adjoint_sum_sq_posSemidef hP hPs A
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hps.isHermitian
    intro x hx
    have hn := hps.dotProduct_mulVec_nonneg x
    have hne : star x ⬝ᵥ ((X A + Y Aᴴ) * (X A + Y Aᴴ)) *ᵥ x ≠ 0 := by
      intro hz
      have hk := hps.dotProduct_mulVec_zero_iff.mp hz
      obtain ⟨hu, hv⟩ := (square_mulVec_zero_iff hP hPs A x).mp hk
      exact hx (hker x hu hv)
    exact lt_of_le_of_ne hn (Ne.symm hne)

/-- Multiplying an odd operator by its grading reverses its square. -/
theorem graded_square (hP : IsIdempotentElem P) (A B : Matrix n n ℝ) :
    (reflection P * (X A + Y B)) * (reflection P * (X A + Y B)) =
      -((X A + Y B) * (X A + Y B)) := by
  calc
    _ = (reflection P * (X A + Y B) * reflection P) * (X A + Y B) := by
      simp only [mul_assoc]
    _ = _ := by rw [conjugate_sum hP A B, neg_mul]

/-- Krein self-adjointness, stated with the actual grading-adjoint formula. -/
theorem graded_krein_selfadjoint (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) :
    reflection P * (reflection P * (X A + Y Aᴴ))ᴴ * reflection P =
      reflection P * (X A + Y Aᴴ) := by
  have hs : (reflection P)ᴴ = reflection P := by
    simp only [reflection, two_mul, conjTranspose_sub, conjTranspose_add,
      conjTranspose_one, hPs.eq]
  rw [conjTranspose_mul, hs, (adjoint_sum_isHermitian hPs A).eq]
  calc
    _ = reflection P * (X A + Y Aᴴ) * (reflection P * reflection P) := by
      simp only [mul_assoc]
    _ = _ := by rw [reflection_sq hP, mul_one]

/-- A nonzero Krein-self-adjoint square need not be positive in the real metric. -/
theorem graded_square_not_posSemidef (hP : IsIdempotentElem P)
    (hPs : P.IsHermitian) (A : Matrix n n ℝ) (hu : X A ≠ 0) :
    ¬((reflection P * (X A + Y Aᴴ)) * (reflection P * (X A + Y Aᴴ))).PosSemidef := by
  intro h
  have hn := h.trace_nonneg
  rw [graded_square hP, trace_neg] at hn
  have ht := (trace_square_pos_iff hP hPs A).mpr hu
  exact (not_le_of_gt (neg_lt_zero.mpr ht)) hn

end InfoGeometry.NCG.OppositePeirceRealMetric
