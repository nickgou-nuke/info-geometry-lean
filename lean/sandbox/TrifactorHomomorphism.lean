import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

namespace InfoGeometry.Modular.DeterminantTrifactor

/-- The Scale component is the multiplicative group of positive real numbers. -/
def ScaleGroup := { x : ℝ // 0 < x }

instance : CommGroup ScaleGroup where
  mul a b := ⟨a.1 * b.1, mul_pos a.2 b.2⟩
  one := ⟨1, zero_lt_one⟩
  inv a := ⟨a.1⁻¹, inv_pos.mpr a.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  mul_inv_cancel a := Subtype.ext (mul_inv_cancel₀ (ne_of_gt a.2))
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

/-- The Parity component is the multiplicative group {1, -1}. -/
def ParityGroup := { x : ℝ // x = 1 ∨ x = -1 }

instance : CommGroup ParityGroup where
  mul a b := ⟨a.1 * b.1, by 
    rcases a.2 with h1 | h2 <;> rcases b.2 with h3 | h4 <;> 
    (subst_vars; norm_num)⟩
  one := ⟨1, Or.inl rfl⟩
  inv a := ⟨a.1⁻¹, by 
    rcases a.2 with h1 | h2 <;> 
    (subst_vars; norm_num)⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  mul_inv_cancel a := Subtype.ext (by 
    rcases a.2 with h1 | h2 <;> 
    (subst_vars; norm_num))
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

/-- The real invertible numbers decompose exactly into Scale and Parity. -/
def realUnitsEquiv : ℝˣ ≃* (ScaleGroup × ParityGroup) where
  toFun u := (⟨|u.val|, abs_pos.mpr u.ne_zero⟩, 
              ⟨Real.sign u.val, by 
                have h := Real.sign_apply_eq u.val
                rcases lt_trichotomy u.val 0 with h1 | h2 | h3
                · right; rw [if_neg (not_lt_of_lt h1), if_pos h1]
                · exfalso; exact u.ne_zero h2
                · left; rw [if_pos h3]⟩)
  invFun p := Units.mk0 (p.1.1 * p.2.1) (by 
    intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact ne_of_gt p.1.2 h1
    · rcases p.2.2 with h3 | h4 <;> subst_vars <;> norm_num at h2)
  left_inv u := Units.ext (by 
    dsimp
    have hz : (u:ℝ) ≠ 0 := u.ne_zero
    rcases lt_trichotomy (u:ℝ) 0 with h1 | h2 | h3
    · have h_sign : Real.sign (u:ℝ) = -1 := by rw [Real.sign_apply_eq, if_neg (not_lt_of_lt h1), if_pos h1]
      have h_abs : |(u:ℝ)| = -(u:ℝ) := abs_of_neg h1
      rw [h_sign, h_abs]; ring
    · exfalso; exact hz h2
    · have h_sign : Real.sign (u:ℝ) = 1 := by rw [Real.sign_apply_eq, if_pos h3]
      have h_abs : |(u:ℝ)| = (u:ℝ) := abs_of_pos h3
      rw [h_sign, h_abs]; ring)
  right_inv p := Prod.ext 
    (Subtype.ext (by 
      dsimp
      rcases p.2.2 with h3 | h4 <;> subst_vars
      · rw [mul_one, abs_of_pos p.1.2]
      · rw [mul_neg_one, abs_neg, abs_of_pos p.1.2]))
    (Subtype.ext (by 
      dsimp
      rcases p.2.2 with h3 | h4 <;> subst_vars
      · rw [mul_one]
        have h_pos : (p.1.val : ℝ) > 0 := p.1.2
        rw [Real.sign_apply_eq, if_pos h_pos]
      · rw [mul_neg_one]
        have h_neg : -(p.1.val : ℝ) < 0 := neg_lt_zero.mpr p.1.2
        rw [Real.sign_apply_eq, if_neg (not_lt_of_lt h_neg), if_pos h_neg]))
  map_mul' x y := Prod.ext 
    (Subtype.ext (abs_mul x.val y.val))
    (Subtype.ext (Real.sign_mul x.val y.val))

end InfoGeometry.Modular.DeterminantTrifactor
