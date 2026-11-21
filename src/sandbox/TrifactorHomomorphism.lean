/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

namespace InfoGeometry.Modular.DeterminantTrifactor

/-- The Scale component is the multiplicative group of positive real numbers. -/
abbrev ScaleGroup := { x : ℝ // 0 < x }

noncomputable instance : CommGroup ScaleGroup where
  mul a b := ⟨a.1 * b.1, mul_pos a.2 b.2⟩
  one := ⟨1, zero_lt_one⟩
  inv a := ⟨a.1⁻¹, inv_pos.mpr a.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := by
    apply Subtype.ext
    change a.1⁻¹ * a.1 = 1
    exact inv_mul_cancel₀ (ne_of_gt a.2)
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

/-- The Parity component is the multiplicative group {1, -1}. -/
abbrev ParityGroup := { x : ℝ // x = 1 ∨ x = -1 }

noncomputable instance : CommGroup ParityGroup where
  mul a b := ⟨a.1 * b.1, by
    rcases a.2 with h1 | h1 <;> rcases b.2 with h2 | h2 <;>
      simp [h1, h2]⟩
  one := ⟨1, Or.inl rfl⟩
  inv a := ⟨a.1⁻¹, by
    rcases a.2 with h1 | h1 <;> simp [h1]⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := by
    apply Subtype.ext
    change a.1⁻¹ * a.1 = 1
    rcases a.2 with h1 | h1 <;> simp [h1]
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

/-- The real invertible numbers decompose exactly into Scale and Parity. -/
noncomputable def realUnitsEquiv : ℝˣ ≃* (ScaleGroup × ParityGroup) where
  toFun u := (⟨|u.val|, abs_pos.mpr u.ne_zero⟩, 
              ⟨Real.sign u.val, by 
                have h := Real.sign_apply_eq u.val
                rcases lt_trichotomy u.val 0 with h1 | h2 | h3
                · right; exact Real.sign_of_neg h1
                · exfalso; exact u.ne_zero h2
                · left; exact Real.sign_of_pos h3⟩)
  invFun p := Units.mk0 (p.1.1 * p.2.1) (by 
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact (ne_of_gt p.1.2) h1
    · rcases p.2.2 with h3 | h3 <;> rw [h3] at h2 <;> norm_num at h2)
  left_inv u := Units.ext (by 
    dsimp
    have hz : (u:ℝ) ≠ 0 := u.ne_zero
    rcases lt_trichotomy (u:ℝ) 0 with h1 | h2 | h3
    · have h_sign : Real.sign (u:ℝ) = -1 := Real.sign_of_neg h1
      have h_abs : |(u:ℝ)| = -(u:ℝ) := abs_of_neg h1
      rw [h_sign, h_abs]; ring
    · exfalso; exact hz h2
    · have h_sign : Real.sign (u:ℝ) = 1 := Real.sign_of_pos h3
      have h_abs : |(u:ℝ)| = (u:ℝ) := abs_of_pos h3
      rw [h_sign, h_abs]; ring)
  right_inv p := Prod.ext
    (Subtype.ext (by
      dsimp
      rcases p.2.2 with h3 | h3
      · rw [h3, mul_one, abs_of_pos p.1.2]
      · rw [h3, mul_neg_one, abs_neg, abs_of_pos p.1.2]))
    (Subtype.ext (by
      dsimp
      rcases p.2.2 with h3 | h3
      · rw [h3, mul_one, Real.sign_of_pos p.1.2]
      · rw [h3, mul_neg_one, Real.sign_of_neg (neg_lt_zero.mpr p.1.2)]))
  map_mul' x y := Prod.ext 
    (Subtype.ext (abs_mul x.val y.val))
    (Subtype.ext (by
      change Real.sign ((x : ℝ) * (y : ℝ)) = Real.sign (x : ℝ) * Real.sign (y : ℝ)
      have hx : (x : ℝ) ≠ 0 := x.ne_zero
      have hy : (y : ℝ) ≠ 0 := y.ne_zero
      rcases hx.lt_or_gt with hxneg | hxpos <;>
        rcases hy.lt_or_gt with hyneg | hypos
      · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg hxneg hyneg),
          Real.sign_of_neg hxneg, Real.sign_of_neg hyneg]
        norm_num
      · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos hxneg hypos),
          Real.sign_of_neg hxneg, Real.sign_of_pos hypos]
        norm_num
      · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hxpos hyneg),
          Real.sign_of_pos hxpos, Real.sign_of_neg hyneg]
        norm_num
      · rw [Real.sign_of_pos (mul_pos hxpos hypos),
          Real.sign_of_pos hxpos, Real.sign_of_pos hypos]
        norm_num))

end InfoGeometry.Modular.DeterminantTrifactor
