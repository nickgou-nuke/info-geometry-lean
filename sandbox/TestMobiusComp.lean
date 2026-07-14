import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace InfoGeometry
def RiemannSphere := Option ℂ
structure MobiusTransform where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

noncomputable def MobiusTransform.eval (M : MobiusTransform) (z : RiemannSphere) : RiemannSphere :=
  match z with
  | none => if M.c = 0 then none else some (M.a / M.c)
  | some z' =>
      let denom := M.c * z' + M.d
      if denom = 0 then none else some ((M.a * z' + M.b) / denom)

def inv (M : MobiusTransform) : MobiusTransform :=
  { a := M.d, b := -M.b, c := -M.c, d := M.a, det_ne_zero := by
      have h := M.det_ne_zero; dsimp; have h_ring : M.d * M.a - -M.b * -M.c = M.a * M.d - M.b * M.c := by ring
      rw [h_ring]; exact h }

def comp (M1 M2 : MobiusTransform) : MobiusTransform :=
  { a := M1.a * M2.a + M1.b * M2.c,
    b := M1.a * M2.b + M1.b * M2.d,
    c := M1.c * M2.a + M1.d * M2.c,
    d := M1.c * M2.b + M1.d * M2.d,
    det_ne_zero := by
      have h1 := M1.det_ne_zero
      have h2 := M2.det_ne_zero
      have h_ring : (M1.a * M2.a + M1.b * M2.c) * (M1.c * M2.b + M1.d * M2.d) -
                    (M1.a * M2.b + M1.b * M2.d) * (M1.c * M2.a + M1.d * M2.c) =
                    (M1.a * M1.d - M1.b * M1.c) * (M2.a * M2.d - M2.b * M2.c) := by ring
      rw [h_ring]
      exact mul_ne_zero h1 h2 }

lemma eval_comp (M1 M2 : MobiusTransform) (z : RiemannSphere) :
    (comp M1 M2).eval z = M1.eval (M2.eval z) := by
  cases z with
  | none =>
    change (if M1.c * M2.a + M1.d * M2.c = 0 then none else some ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c))) =
           M1.eval (if M2.c = 0 then none else some (M2.a / M2.c))
    by_cases h2c : M2.c = 0
    · rw [if_pos h2c]
      change (if M1.c * M2.a + M1.d * M2.c = 0 then none else some _) =
             (if M1.c = 0 then none else some (M1.a / M1.c))
      have hc : M1.c * M2.a + M1.d * M2.c = M1.c * M2.a := by rw [h2c, mul_zero, add_zero]
      have ha : M1.a * M2.a + M1.b * M2.c = M1.a * M2.a := by rw [h2c, mul_zero, add_zero]
      by_cases h1c : M1.c = 0
      · have : M1.c * M2.a + M1.d * M2.c = 0 := by rw [hc, h1c, zero_mul]
        rw [if_pos this, if_pos h1c]
      · have h2a : M2.a ≠ 0 := by
          intro ha_zero
          have h_det2 := M2.det_ne_zero
          rw [h2c, ha_zero, zero_mul, mul_zero, sub_zero] at h_det2
          exact h_det2 rfl
        have : M1.c * M2.a + M1.d * M2.c ≠ 0 := by
          rw [hc]
          exact mul_ne_zero h1c h2a
        rw [if_neg this, if_neg h1c]
        congr 1
        change ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c)) = M1.a / M1.c
        rw [hc, ha]
        field_simp
    · rw [if_neg h2c]
      change (if M1.c * M2.a + M1.d * M2.c = 0 then none else some _) =
             (if M1.c * (M2.a / M2.c) + M1.d = 0 then none else some _)
      have h_denom : M1.c * (M2.a / M2.c) + M1.d = 0 ↔ M1.c * M2.a + M1.d * M2.c = 0 := by
        constructor
        · intro h
          calc M1.c * M2.a + M1.d * M2.c
            _ = (M1.c * (M2.a / M2.c) + M1.d) * M2.c := by
              have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by
                rw [mul_assoc, div_mul_cancel₀ _ h2c]
              rw [add_mul, this]
            _ = 0 * M2.c := by rw [h]
            _ = 0 := zero_mul M2.c
        · intro h
          have h_eq : (M1.c * (M2.a / M2.c) + M1.d) * M2.c = 0 := by
            calc (M1.c * (M2.a / M2.c) + M1.d) * M2.c
              _ = M1.c * (M2.a / M2.c) * M2.c + M1.d * M2.c := by ring
              _ = M1.c * M2.a + M1.d * M2.c := by
                have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2c]
                rw [this]
              _ = 0 := h
          exact (mul_eq_zero.mp h_eq).resolve_right h2c
      by_cases h_c_zero : M1.c * M2.a + M1.d * M2.c = 0
      · rw [if_pos h_c_zero, if_pos (h_denom.mpr h_c_zero)]
      · rw [if_neg h_c_zero, if_neg (mt h_denom.mp h_c_zero)]
        congr 1
        have h_c_zero' : M1.c * (M2.a / M2.c) + M1.d ≠ 0 := mt h_denom.mp h_c_zero
        change ((M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c)) =
               (M1.a * (M2.a / M2.c) + M1.b) / (M1.c * (M2.a / M2.c) + M1.d)
        have num_eq : (M1.a * (M2.a / M2.c) + M1.b) = (M1.a * M2.a + M1.b * M2.c) / M2.c := by
          rw [eq_div_iff_mul_eq h2c]
          calc (M1.a * (M2.a / M2.c) + M1.b) * M2.c
            _ = M1.a * (M2.a / M2.c) * M2.c + M1.b * M2.c := by ring
            _ = M1.a * M2.a + M1.b * M2.c := by
              have : M1.a * (M2.a / M2.c) * M2.c = M1.a * M2.a := by rw [mul_assoc, div_mul_cancel₀ _ h2c]
              rw [this]
        have den_eq : (M1.c * (M2.a / M2.c) + M1.d) = (M1.c * M2.a + M1.d * M2.c) / M2.c := by
          rw [eq_div_iff_mul_eq h2c]
          calc (M1.c * (M2.a / M2.c) + M1.d) * M2.c
            _ = M1.c * (M2.a / M2.c) * M2.c + M1.d * M2.c := by ring
            _ = M1.c * M2.a + M1.d * M2.c := by
              have : M1.c * (M2.a / M2.c) * M2.c = M1.c * M2.a := by rw [mul_assoc, div_mul_cancel₀ _ h2c]
              rw [this]
        rw [num_eq, den_eq]
        have cross : (M1.a * M2.a + M1.b * M2.c) / M2.c / ((M1.c * M2.a + M1.d * M2.c) / M2.c) = (M1.a * M2.a + M1.b * M2.c) / (M1.c * M2.a + M1.d * M2.c) := by
          rw [div_div_div_cancel_right₀ h2c]
        rw [cross]
  | some z' =>
    change (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
           M1.eval (if M2.c * z' + M2.d = 0 then none else some _)
    by_cases h2_denom : M2.c * z' + M2.d = 0
    · rw [if_pos h2_denom]
      change (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
             (if M1.c = 0 then none else some (M1.a / M1.c))
      have hc : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = M1.c * (M2.a * z' + M2.b) := by
        calc (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)
          _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by ring
          _ = M1.c * (M2.a * z' + M2.b) + M1.d * 0 := by rw [h2_denom]
          _ = M1.c * (M2.a * z' + M2.b) := by ring
      have ha : (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d) = M1.a * (M2.a * z' + M2.b) := by
        calc (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)
          _ = M1.a * (M2.a * z' + M2.b) + M1.b * (M2.c * z' + M2.d) := by ring
          _ = M1.a * (M2.a * z' + M2.b) + M1.b * 0 := by rw [h2_denom]
          _ = M1.a * (M2.a * z' + M2.b) := by ring
      by_cases h1c : M1.c = 0
      · have : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 := by
          rw [hc, h1c, zero_mul]
        rw [if_pos this, if_pos h1c]
      · have h2a : M2.a * z' + M2.b ≠ 0 := by
          intro h_zero
          have h_det2 := M2.det_ne_zero
          have : (M2.a * z' + M2.b) * M2.c - (M2.c * z' + M2.d) * M2.a = M2.b * M2.c - M2.d * M2.a := by ring
          rw [h_zero, h2_denom, zero_mul, zero_mul, zero_sub] at this
          have h_det2_neg : M2.b * M2.c - M2.a * M2.d = 0 := by
            calc M2.b * M2.c - M2.a * M2.d
              _ = M2.b * M2.c - M2.d * M2.a := by ring
              _ = -0 := this.symm
              _ = 0 := neg_zero
          have h_det2_pos : M2.a * M2.d - M2.b * M2.c = 0 := by
            calc M2.a * M2.d - M2.b * M2.c
              _ = - (M2.b * M2.c - M2.a * M2.d) := by ring
              _ = - 0 := by rw [h_det2_neg]
              _ = 0 := neg_zero
          exact h_det2 h_det2_pos
        have : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) ≠ 0 := by
          rw [hc]
          exact mul_ne_zero h1c h2a
        rw [if_neg this, if_neg h1c]
        congr 1
        change ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) / ((M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)) = M1.a / M1.c
        rw [hc, ha]
        have : M1.a * (M2.a * z' + M2.b) / (M1.c * (M2.a * z' + M2.b)) = M1.a / M1.c := by
          rw [mul_comm M1.a, mul_comm M1.c]
          rw [mul_div_mul_left _ _ h2a]
        exact this
    · rw [if_neg h2_denom]
      change (if (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 then none else some _) =
             (if M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d = 0 then none else some _)
      have h_denom : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d = 0 ↔ (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0 := by
        constructor
        · intro h
          calc (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)
            _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by ring
            _ = (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d) := by
              have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
              rw [add_mul, this]
            _ = 0 * (M2.c * z' + M2.d) := by rw [h]
            _ = 0 := zero_mul _
        · intro h
          have h_eq : (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d) = 0 := by
            calc (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d)
              _ = M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) + M1.d * (M2.c * z' + M2.d) := by ring
              _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
                have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                  rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
                rw [this]
              _ = (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) := by ring
              _ = 0 := h
          exact (mul_eq_zero.mp h_eq).resolve_right h2_denom
      by_cases h_c_zero : (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) = 0
      · rw [if_pos h_c_zero, if_pos (h_denom.mpr h_c_zero)]
      · rw [if_neg h_c_zero, if_neg (mt h_denom.mp h_c_zero)]
        congr 1
        change ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) / ((M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)) =
               (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) / (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d)
        have num_eq : (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) = ((M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d)) / (M2.c * z' + M2.d) := by
          rw [eq_div_iff_mul_eq h2_denom]
          calc (M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.b) * (M2.c * z' + M2.d)
            _ = M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) + M1.b * (M2.c * z' + M2.d) := by ring
            _ = M1.a * (M2.a * z' + M2.b) + M1.b * (M2.c * z' + M2.d) := by
              have : M1.a * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.a * (M2.a * z' + M2.b) := by
                rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
              rw [this]
            _ = (M1.a * M2.a + M1.b * M2.c) * z' + (M1.a * M2.b + M1.b * M2.d) := by ring
        have den_eq : (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) = ((M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d)) / (M2.c * z' + M2.d) := by
          rw [eq_div_iff_mul_eq h2_denom]
          calc (M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) + M1.d) * (M2.c * z' + M2.d)
            _ = M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) + M1.d * (M2.c * z' + M2.d) := by ring
            _ = M1.c * (M2.a * z' + M2.b) + M1.d * (M2.c * z' + M2.d) := by
              have : M1.c * ((M2.a * z' + M2.b) / (M2.c * z' + M2.d)) * (M2.c * z' + M2.d) = M1.c * (M2.a * z' + M2.b) := by
                rw [mul_assoc, div_mul_cancel₀ _ h2_denom]
              rw [this]
            _ = (M1.c * M2.a + M1.d * M2.c) * z' + (M1.c * M2.b + M1.d * M2.d) := by ring
        rw [num_eq, den_eq]
        rw [div_div_div_cancel_right₀ h2_denom]
