/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Circle
import Mathlib
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.DeterminantTrifactor

/-- The Scale component is the multiplicative group of positive real numbers. -/
def ScaleGroup := { x : ℝ // 0 < x }

noncomputable instance : CommGroup ScaleGroup where
  mul a b := ⟨a.1 * b.1, mul_pos a.2 b.2⟩
  one := ⟨1, zero_lt_one⟩
  inv a := ⟨a.1⁻¹, inv_pos.mpr a.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel₀ (ne_of_gt a.2))
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

/-- The Parity component is the multiplicative group {1, -1}. -/
def ParityGroup := { x : ℝ // x = 1 ∨ x = -1 }

noncomputable instance : CommGroup ParityGroup where
  mul a b := ⟨a.1 * b.1, by
    rcases a.2 with ha | ha <;> rcases b.2 with hb | hb
    · exact Or.inl (by rw [ha, hb]; norm_num)
    · exact Or.inr (by rw [ha, hb]; norm_num)
    · exact Or.inr (by rw [ha, hb]; norm_num)
    · exact Or.inl (by rw [ha, hb]; norm_num)⟩
  one := ⟨1, Or.inl rfl⟩
  inv a := ⟨a.1⁻¹, by
    rcases a.2 with ha | ha
    · exact Or.inl (by rw [ha]; norm_num)
    · exact Or.inr (by rw [ha]; norm_num)⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := Subtype.ext (by
    change a.1⁻¹ * a.1 = 1
    have ha : a.1 ≠ 0 := by
      rcases a.2 with h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num
    exact inv_mul_cancel₀ ha)
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

/-- The Chiral Phase component is the complex unit circle U(1). -/
abbrev PhaseGroup := Circle

private lemma realSign_eq_signType (x : ℝ) :
    Real.sign x = (SignType.sign x : ℝ) := by
  by_cases hp : 0 < x <;> by_cases hn : x < 0 <;>
    simp [Real.sign, sign_apply, hp, hn] <;> linarith

private lemma realSign_mul_abs (x : ℝ) : |x| * Real.sign x = x := by
  rw [realSign_eq_signType]
  exact abs_mul_sign x

/-- The real invertible numbers decompose exactly into Scale and Parity. -/
def realUnitsEquiv : ℝˣ ≃* (ScaleGroup × ParityGroup) where
  toFun u := (⟨|u.val|, abs_pos.mpr u.ne_zero⟩, 
              ⟨Real.sign u.val, by 
                rcases Real.sign_apply_eq_of_ne_zero u.val u.ne_zero with h | h
                · exact Or.inr h
                · exact Or.inl h⟩)
  invFun p := Units.mk0 (p.1.1 * p.2.1) (by 
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact ne_of_gt p.1.2 h1
    · rcases p.2.2 with h3 | h4
      · rw [h3] at h2
        norm_num at h2
      · rw [h4] at h2
        norm_num at h2)
  left_inv u := Units.ext (by
    dsimp
    exact realSign_mul_abs u.val)
  right_inv p := Prod.ext 
    (Subtype.ext (by
      dsimp
      rcases p.2.2 with h | h
      · rw [h, mul_one, abs_of_pos p.1.2]
      · rw [h, mul_neg_one, abs_neg, abs_of_pos p.1.2]))
    (Subtype.ext (by
      dsimp
      rcases p.2.2 with h | h
      · rw [h, mul_one, Real.sign_of_pos p.1.2]
      · rw [h, mul_neg_one, Real.sign_of_neg (neg_lt_zero.mpr p.1.2)]))
  map_mul' x y := Prod.ext 
    (Subtype.ext (abs_mul x.val y.val))
    (Subtype.ext (by
      change Real.sign (x.val * y.val) = Real.sign x.val * Real.sign y.val
      rw [realSign_eq_signType (x.val * y.val), realSign_eq_signType x.val,
        realSign_eq_signType y.val]
      simpa using congrArg (fun z : SignType => (z : ℝ)) (sign_mul x.val y.val)))

/-- The complex invertible numbers decompose exactly into Scale and Phase. -/
def complexUnitsEquiv : ℂˣ ≃* (ScaleGroup × PhaseGroup) where
  toFun u := (⟨‖u.val‖, norm_pos_iff.mpr u.ne_zero⟩,
              ⟨u.val / (‖u.val‖ : ℂ), by
                apply (mem_sphere_zero_iff_norm).2
                rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _)]
                exact div_self (ne_of_gt (norm_pos_iff.mpr u.ne_zero))⟩)
  invFun p := Units.mk0 (p.1.1 * p.2.1) (by 
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · have h_pos := p.1.2; rw [← Complex.ofReal_zero, Complex.ofReal_inj] at h1
      exact ne_of_gt h_pos h1
    · have h_norm := p.2.norm_coe
      rw [h2] at h_norm
      norm_num at h_norm)
  left_inv u := Units.ext (by 
    dsimp
    have hnz : (‖(u:ℂ)‖ : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (norm_pos_iff.mpr u.ne_zero)
    exact mul_div_cancel₀ (u:ℂ) hnz)
  right_inv p := Prod.ext 
    (Subtype.ext (by
      dsimp
      rw [norm_mul, Complex.norm_of_nonneg (le_of_lt p.1.2), Circle.norm_coe, mul_one]))
    (Subtype.ext (by 
      dsimp
      have h_abs_pos : (p.1.val : ℝ) > 0 := p.1.2
      have h_abs : ‖(p.1.val : ℂ) * p.2.val‖ = p.1.val := by
        rw [norm_mul, Complex.norm_of_nonneg (le_of_lt h_abs_pos), Circle.norm_coe, mul_one]
      rw [h_abs]
      have hnz : (p.1.val : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]
        exact ne_of_gt h_abs_pos
      exact mul_div_cancel_left₀ (p.2.val) hnz))
  map_mul' x y := Prod.ext 
    (Subtype.ext (norm_mul x.val y.val))
    (Subtype.ext (by 
      dsimp
      rw [norm_mul, Complex.ofReal_mul]
      calc
        (x.val * y.val) / (↑‖x.val‖ * ↑‖y.val‖) =
          (x.val / ↑‖x.val‖) * (y.val / ↑‖y.val‖) := by
            have hx : (↑‖x.val‖ : ℂ) ≠ 0 := by
              exact_mod_cast (norm_pos_iff.mpr x.ne_zero).ne'
            have hy : (↑‖y.val‖ : ℂ) ≠ 0 := by
              exact_mod_cast (norm_pos_iff.mpr y.ne_zero).ne'
            field_simp [hx, hy]
            ))

end InfoGeometry.Modular.DeterminantTrifactor

end
