/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coercivity from an actual bounded contracting homotopy

All operators act on a real Hilbert space. No coefficient commutation is used.
The homotopy identity and its norm bound are explicit hypotheses, not a claim
that an interacting model supplies them. Nilpotence is not needed for the
inequality itself; it is needed for its interpretation as a complex.
-/

namespace InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The positive Hodge operator made from the native Hilbert adjoint. -/
noncomputable def hodge (d : E →L[ℝ] E) : E →L[ℝ] E :=
  d * adjoint d + adjoint d * d

/-- Self-adjointness is proved using the native operator star. -/
theorem hodge_selfAdjoint (d : E →L[ℝ] E) : IsSelfAdjoint (hodge d) := by
  change star (d * star d + star d * d) = d * star d + star d * d
  simp only [star_add, star_mul, star_star]

theorem inner_hodge (d : E →L[ℝ] E) (x : E) :
    inner ℝ x (hodge d x) = ‖d x‖ ^ 2 + ‖adjoint d x‖ ^ 2 := by
  have h₁ : inner ℝ x (d (adjoint d x)) = ‖adjoint d x‖ ^ 2 := by
    have h := adjoint_inner_right (adjoint d) x (adjoint d x)
    simpa only [adjoint_adjoint, real_inner_self_eq_norm_sq] using h
  have h₂ : inner ℝ x (adjoint d (d x)) = ‖d x‖ ^ 2 := by
    rw [adjoint_inner_right, real_inner_self_eq_norm_sq]
  change inner ℝ x (d (adjoint d x) + adjoint d (d x)) = _
  rw [inner_add_right, h₁, h₂, add_comm]

theorem inner_hodge_nonneg (d : E →L[ℝ] E) (x : E) :
    0 ≤ inner ℝ x (hodge d x) := by
  rw [inner_hodge]
  positivity

theorem hodge_apply_eq_zero_iff (d : E →L[ℝ] E) (x : E) :
    hodge d x = 0 ↔ d x = 0 ∧ adjoint d x = 0 := by
  constructor
  · intro hx
    have he := inner_hodge d x
    rw [hx, inner_zero_right] at he
    have hd : ‖d x‖ = 0 := by nlinarith [sq_nonneg ‖adjoint d x‖]
    have ha : ‖adjoint d x‖ = 0 := by nlinarith [sq_nonneg ‖d x‖]
    exact ⟨norm_eq_zero.mp hd, norm_eq_zero.mp ha⟩
  · rintro ⟨hd, ha⟩
    change d (adjoint d x) + adjoint d (d x) = 0
    simp [hd, ha]

/-- The native kernel is the actual intersection of the two kernels. -/
theorem hodge_ker (d : E →L[ℝ] E) :
    (hodge d).ker = d.ker ⊓ (adjoint d).ker := by
  ext x
  exact hodge_apply_eq_zero_iff d x

/-- First-order estimate derived by applying the contracting identity to x. -/
theorem norm_le_of_homotopy
    (d h P : E →L[ℝ] E) (hcontract : d * h + h * d = 1 - P)
    {C : ℝ} (hbound : ‖h‖ ≤ C) (x : E) (hx : P x = 0) :
    ‖x‖ ≤ C * (‖d x‖ + ‖adjoint d x‖) := by
  have hstate : d (h x) + h (d x) = x := by
    have he := congrArg (fun T : E →L[ℝ] E => T x) hcontract
    change d (h x) + h (d x) = x - P x at he
    simpa only [hx, sub_zero] using he
  have hh : ‖h x‖ ≤ C * ‖x‖ :=
    (h.le_opNorm x).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg x))
  have hha : ‖adjoint h x‖ ≤ C * ‖x‖ := by
    have hn : ‖adjoint h‖ = ‖h‖ := adjoint.norm_map h
    exact ((adjoint h).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by simpa only [hn] using hbound) (norm_nonneg x))
  have hestimate : ‖x‖ * ‖x‖ ≤
      (C * (‖d x‖ + ‖adjoint d x‖)) * ‖x‖ := by
    calc
      _ = inner ℝ x (d (h x) + h (d x)) := by
        rw [hstate, real_inner_self_eq_norm_sq, pow_two]
      _ = inner ℝ (adjoint d x) (h x) + inner ℝ (adjoint h x) (d x) := by
        rw [inner_add_right, ← adjoint_inner_left d (h x) x,
          ← adjoint_inner_left h (d x) x]
      _ ≤ ‖adjoint d x‖ * ‖h x‖ + ‖adjoint h x‖ * ‖d x‖ :=
        add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
      _ ≤ ‖adjoint d x‖ * (C * ‖x‖) + (C * ‖x‖) * ‖d x‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hha (norm_nonneg _))
      _ = _ := by ring
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hx0)).mp hestimate

/-- A common homotopy bound yields a common positive coercivity constant.
The model must still construct h and prove its bound. -/
theorem coercivity_of_homotopy
    (d h P : E →L[ℝ] E) (hcontract : d * h + h * d = 1 - P)
    {C : ℝ} (hC : 0 < C) (hbound : ‖h‖ ≤ C) (x : E) (hx : P x = 0) :
    (1 / (2 * C ^ 2)) * ‖x‖ ^ 2 ≤ inner ℝ x (hodge d x) := by
  have hn := norm_le_of_homotopy d h P hcontract hbound x hx
  have hs := mul_self_le_mul_self (norm_nonneg x) hn
  have ht : (‖d x‖ + ‖adjoint d x‖) ^ 2 ≤
      2 * (‖d x‖ ^ 2 + ‖adjoint d x‖ ^ 2) := by
    nlinarith [sq_nonneg (‖d x‖ - ‖adjoint d x‖)]
  have hm := mul_le_mul_of_nonneg_left ht (sq_nonneg C)
  have he : ‖x‖ ^ 2 ≤ (2 * C ^ 2) * (‖d x‖ ^ 2 + ‖adjoint d x‖ ^ 2) := by
    nlinarith [hs, hm]
  rw [inner_hodge]
  calc
    _ = ‖x‖ ^ 2 / (2 * C ^ 2) := by ring
    _ ≤ _ := (div_le_iff₀ (by positivity : 0 < 2 * C ^ 2)).mpr (by nlinarith [he])

/-- Any nonnegative extra quadratic-form contribution preserves the bound.
No commutation between H and the differential is required. -/
theorem coercivity_of_form_domination
    (d h P H : E →L[ℝ] E) (hcontract : d * h + h * d = 1 - P)
    {C : ℝ} (hC : 0 < C) (hbound : ‖h‖ ≤ C)
    (hdom : ∀ x, inner ℝ x (hodge d x) ≤ inner ℝ x (H x))
    (x : E) (hx : P x = 0) :
    (1 / (2 * C ^ 2)) * ‖x‖ ^ 2 ≤ inner ℝ x (H x) :=
  (coercivity_of_homotopy d h P hcontract hC hbound x hx).trans (hdom x)

end InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity
