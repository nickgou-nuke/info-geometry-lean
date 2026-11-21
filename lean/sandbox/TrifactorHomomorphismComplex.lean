/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Circle
import Mathlib
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic
import sandbox.TrifactorHomomorphism

namespace InfoGeometry.Modular.DeterminantTrifactor

noncomputable abbrev complexAbs (z : ℂ) : ℝ := ‖z‖

private theorem complexAbs_pos {z : ℂ} (hz : z ≠ 0) : 0 < complexAbs z :=
  norm_pos_iff.mpr hz

private theorem complexAbs_mul (z w : ℂ) : complexAbs (z * w) = complexAbs z * complexAbs w :=
  Complex.norm_mul z w

private theorem complexAbs_of_pos {r : ℝ} (hr : 0 < r) : complexAbs (r : ℂ) = r := by
  simpa [complexAbs] using hr.le

private theorem circle_norm (z : Circle) : complexAbs (z : ℂ) = 1 := by
  have hz : (z : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := z.property
  rw [mem_sphere_zero_iff_norm] at hz
  exact hz

/- The positive scale and parity factors are imported from the real owner so
the two decompositions share one kernel-checked implementation. -/

/-- The Chiral Phase component is the unit circle, kept as an auxiliary
algebraic phase group rather than as the scalar field of the real carriers. -/
abbrev PhaseGroup := Circle

/-- The complex invertible numbers decompose exactly into Scale and Phase. -/
noncomputable def complexUnitsEquiv : ℂˣ ≃* (ScaleGroup × PhaseGroup) where
  toFun u := (⟨complexAbs u.val, complexAbs_pos u.ne_zero⟩,
              ⟨u.val / complexAbs u.val, by
                apply mem_sphere_zero_iff_norm.mpr
                rw [Complex.norm_div]
                change complexAbs u.val / complexAbs (complexAbs u.val : ℂ) = 1
                rw [complexAbs_of_pos (complexAbs_pos u.ne_zero)]
                have hnz : complexAbs u.val ≠ 0 := ne_of_gt (complexAbs_pos u.ne_zero)
                exact div_self hnz⟩)
  invFun p := Units.mk0 (p.1.1 * p.2.1) (by 
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · have h_pos := p.1.2; rw [← Complex.ofReal_zero, Complex.ofReal_inj] at h1
      exact ne_of_gt h_pos h1
    · have h_norm := p.2.property
      have hnorm : complexAbs (p.2.val) = 1 := circle_norm p.2
      rw [h2] at hnorm
      norm_num [complexAbs] at hnorm)
  left_inv u := Units.ext (by 
    dsimp
    have hnz : (complexAbs (u:ℂ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (complexAbs_pos u.ne_zero)
    exact mul_div_cancel₀ (u:ℂ) hnz)
  right_inv p := Prod.ext 
    (Subtype.ext (by 
      dsimp
      rw [complexAbs_mul, complexAbs_of_pos p.1.2]
      have habs : complexAbs p.2.val = 1 := circle_norm p.2
      rw [habs, mul_one]))
    (Subtype.ext (by 
      dsimp
      have h_abs_pos : (p.1.val : ℝ) > 0 := p.1.2
      have h_abs : complexAbs (p.1.val * p.2.val) = p.1.val := by
        rw [complexAbs_mul, complexAbs_of_pos h_abs_pos]
        have habs : complexAbs p.2.val = 1 := circle_norm p.2
        rw [habs, mul_one]
      rw [h_abs]
      have hnz : (p.1.val : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]
        exact ne_of_gt h_abs_pos
      exact mul_div_cancel_left₀ (p.2.val) hnz))
  map_mul' x y := Prod.ext 
    (Subtype.ext (complexAbs_mul x.val y.val))
    (Subtype.ext (by 
      dsimp
      rw [complexAbs_mul, Complex.ofReal_mul]
      calc
        (x.val * y.val) / (↑(complexAbs x.val) * ↑(complexAbs y.val)) =
          (x.val / ↑(complexAbs x.val)) * (y.val / ↑(complexAbs y.val)) := by
            field_simp [complexAbs_pos x.ne_zero, complexAbs_pos y.ne_zero]))

end InfoGeometry.Modular.DeterminantTrifactor
