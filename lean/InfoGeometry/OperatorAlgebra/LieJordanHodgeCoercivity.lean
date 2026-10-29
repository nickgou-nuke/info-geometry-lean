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
# Quantitative Hodge coercivity from a bounded operator homotopy

The carrier is an arbitrary real Hilbert space and d,h,P are actual bounded
operators. The homotopy equation and its bound are explicit hypotheses; no
uniform bound for an interacting model is postulated as a theorem. Neither
nilpotence nor projection properties are needed for this quantitative step.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanHodgeCoercivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The adjoint Hodge energy is a sum of two squares on the actual carrier. -/
theorem hodge_energy (d : E →L[ℝ] E) (x : E) :
    inner ℝ x ((d * d.adjoint + d.adjoint * d) x) =
      ‖d.adjoint x‖ ^ 2 + ‖d x‖ ^ 2 := by
  change inner ℝ x (d (d.adjoint x) + d.adjoint (d x)) = _
  rw [inner_add_right, ← ContinuousLinearMap.adjoint_inner_left d (d.adjoint x) x,
    ContinuousLinearMap.adjoint_inner_right d x (d x)]
  simp only [real_inner_self_eq_norm_sq]

/-- A bounded homotopy controls vectors in the kernel of the named P. -/
theorem norm_le_of_homotopy
    (d h P : E →L[ℝ] E) (C : ℝ) (hbound : ‖h‖ ≤ C)
    (hhom : d * h + h * d = 1 - P) (x : E) (hx : P x = 0) :
    ‖x‖ ≤ C * (‖d.adjoint x‖ + ‖d x‖) := by
  by_cases hz : x = 0
  · simp [hz]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hz
  have heq := congrArg (fun t : E →L[ℝ] E => t x) hhom
  change d (h x) + h (d x) = x - P x at heq
  rw [hx, sub_zero] at heq
  have he : ‖x‖ ^ 2 =
      inner ℝ (d.adjoint x) (h x) + inner ℝ x (h (d x)) := by
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_add_right,
      heq, real_inner_self_eq_norm_sq]
  have hb₁ : ‖h x‖ ≤ C * ‖x‖ :=
    (h.le_opNorm x).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg x))
  have hb₂ : ‖h (d x)‖ ≤ C * ‖d x‖ :=
    (h.le_opNorm (d x)).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  have hnorm : ‖x‖ * ‖x‖ ≤ ‖x‖ * (C * (‖d.adjoint x‖ + ‖d x‖)) := by
    calc
      _ = inner ℝ (d.adjoint x) (h x) + inner ℝ x (h (d x)) := by
        simpa only [pow_two] using he
      _ ≤ ‖d.adjoint x‖ * ‖h x‖ + ‖x‖ * ‖h (d x)‖ :=
        add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
      _ ≤ ‖d.adjoint x‖ * (C * ‖x‖) + ‖x‖ * (C * ‖d x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hb₁ (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hb₂ (norm_nonneg _))
      _ = _ := by ring
  by_contra hnot
  have hlt : C * (‖d.adjoint x‖ + ‖d x‖) < ‖x‖ := lt_of_not_ge hnot
  have hpos := mul_pos hr (sub_pos.mpr hlt)
  nlinarith only [hpos, hnorm]

/-- Division-free form of the estimate; C is a norm bound, not a spectral input. -/
theorem squared_norm_le_energy
    (d h P : E →L[ℝ] E) (C : ℝ) (hbound : ‖h‖ ≤ C)
    (hhom : d * h + h * d = 1 - P) (x : E) (hx : P x = 0) :
    ‖x‖ ^ 2 ≤ 2 * C ^ 2 * (‖d.adjoint x‖ ^ 2 + ‖d x‖ ^ 2) := by
  have hn := norm_le_of_homotopy d h P C hbound hhom x hx
  have hs := mul_self_le_mul_self (norm_nonneg x) hn
  have hp : (‖d.adjoint x‖ + ‖d x‖) ^ 2 ≤
      2 * (‖d.adjoint x‖ ^ 2 + ‖d x‖ ^ 2) := by
    nlinarith only [sq_nonneg (‖d.adjoint x‖ - ‖d x‖)]
  calc
    ‖x‖ ^ 2 ≤ (C * (‖d.adjoint x‖ + ‖d x‖)) ^ 2 := by
      simpa only [pow_two] using hs
    _ = C ^ 2 * (‖d.adjoint x‖ + ‖d x‖) ^ 2 := by ring
    _ ≤ C ^ 2 * (2 * (‖d.adjoint x‖ ^ 2 + ‖d x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg C)
    _ = _ := by ring

/-- Quantitative coercivity on ker P, with its positive constant displayed. -/
theorem energy_ge_of_homotopy
    (d h P : E →L[ℝ] E) (C : ℝ) (hC : 0 < C) (hbound : ‖h‖ ≤ C)
    (hhom : d * h + h * d = 1 - P) (x : E) (hx : P x = 0) :
    (1 / (2 * C ^ 2)) * ‖x‖ ^ 2 ≤
      inner ℝ x ((d * d.adjoint + d.adjoint * d) x) := by
  rw [hodge_energy]
  have hden : 0 < 2 * C ^ 2 := by positivity
  have hs := squared_norm_le_energy d h P C hbound hhom x hx
  have hd : ‖x‖ ^ 2 / (2 * C ^ 2) ≤
      ‖d.adjoint x‖ ^ 2 + ‖d x‖ ^ 2 :=
    (div_le_iff₀ hden).2 (by simpa only [mul_comm] using hs)
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hd

/-- The same bound applies to the complementary component when P is idempotent. -/
theorem complement_coercivity
    (d h P : E →L[ℝ] E) (hP : P * P = P)
    (C : ℝ) (hC : 0 < C) (hbound : ‖h‖ ≤ C)
    (hhom : d * h + h * d = 1 - P) (x : E) :
    (1 / (2 * C ^ 2)) * ‖x - P x‖ ^ 2 ≤
      inner ℝ (x - P x) ((d * d.adjoint + d.adjoint * d) (x - P x)) := by
  apply energy_ge_of_homotopy d h P C hC hbound hhom
  have hpx := congrArg (fun t : E →L[ℝ] E => t x) hP
  change P (P x) = P x at hpx
  rw [map_sub, hpx, sub_self]

/-- A finite-dimensional pointwise homotopy bound supplies the bounded-operator
hypothesis without imposing a different norm on a concrete carrier. -/
omit [CompleteSpace E] in
theorem linear_energy_ge_of_homotopy [FiniteDimensional ℝ E]
    (d h P : Module.End ℝ E) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ x : E, ‖h x‖ ≤ C * ‖x‖)
    (hhom : d * h + h * d = 1 - P) (x : E) (hx : P x = 0) :
    (1 / (2 * C ^ 2)) * ‖x‖ ^ 2 ≤
      inner ℝ x ((d * d.adjoint + d.adjoint * d) x) := by
  have := FiniteDimensional.complete ℝ E
  let dc : E →L[ℝ] E := LinearMap.toContinuousLinearMap d
  let hc : E →L[ℝ] E := LinearMap.toContinuousLinearMap h
  let pc : E →L[ℝ] E := LinearMap.toContinuousLinearMap P
  have hb : ‖hc‖ ≤ C := ContinuousLinearMap.opNorm_le_bound hc hC.le hbound
  have hh : dc * hc + hc * dc = 1 - pc := by
    ext y
    exact congrArg (fun t : Module.End ℝ E => t y) hhom
  have he := energy_ge_of_homotopy dc hc pc C hC hb hh x hx
  dsimp only [dc] at he
  rw [← LinearMap.adjoint_toContinuousLinearMap] at he
  exact he

end InfoGeometry.OperatorAlgebra.LieJordanHodgeCoercivity
