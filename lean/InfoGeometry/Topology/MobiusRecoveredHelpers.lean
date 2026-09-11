import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# MobiusRecoveredHelpers

Importable helper packet for Möbius inverse and composition laws.
-/

namespace InfoGeometry.Topology.MobiusRecoveredHelpers

open Complex

abbrev RiemannSphere := InfoGeometry.RiemannSphere
abbrev MobiusTransform := InfoGeometry.MobiusTransform

namespace MobiusTransform

noncomputable def eval (M : MobiusTransform) (z : RiemannSphere) : RiemannSphere :=
  InfoGeometry.MobiusTransform.eval M z

def equiv (M1 M2 : MobiusTransform) : Prop :=
  InfoGeometry.MobiusTransform.equiv M1 M2

end MobiusTransform

/-- The inverse Möbius transform. -/
def inv (M : MobiusTransform) : MobiusTransform :=
  { a := M.d,
    b := -M.b,
    c := -M.c,
    d := M.a,
    det_ne_zero := by
      have h := M.det_ne_zero
      dsimp
      have h_ring : M.d * M.a - -M.b * -M.c = M.a * M.d - M.b * M.c := by ring
      rw [h_ring]
      exact h }

/-- Composition of Möbius transforms. -/
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

lemma eval_inv (M : MobiusTransform) (z : RiemannSphere) :
    M.eval ((inv M).eval z) = z := by
  cases z with
  | none =>
    change M.eval (if -M.c = 0 then none else some (M.d / -M.c)) = none
    by_cases hc : M.c = 0
    · have hmc : -M.c = 0 := by rw [hc, neg_zero]
      rw [if_pos hmc]
      change (if M.c = 0 then none else some (M.a / M.c)) = none
      rw [if_pos hc]
    · have hmc : -M.c ≠ 0 := by intro h; apply hc; exact neg_eq_zero.mp h
      rw [if_neg hmc]
      change (if M.c * (M.d / -M.c) + M.d = 0 then none else some _) = none
      have h_denom : M.c * (M.d / -M.c) + M.d = 0 := by
        field_simp; ring
      rw [if_pos h_denom]
  | some z' =>
    change M.eval (if -M.c * z' + M.a = 0 then none else some ((M.d * z' + -M.b) / (-M.c * z' + M.a))) = some z'
    by_cases h_inv_denom : -M.c * z' + M.a = 0
    · rw [if_pos h_inv_denom]
      have hc : M.c ≠ 0 := by
        intro h
        have ha : M.a = 0 := by
          calc M.a = (-M.c * z' + M.a) + M.c * z' := by ring
          _ = 0 + M.c * z' := by rw [h_inv_denom]
          _ = 0 + 0 * z' := by rw [h]
          _ = 0 := by ring
        have h_det := M.det_ne_zero
        rw [h, ha] at h_det
        have h_zero : (0 : ℂ) * M.d - M.b * 0 = 0 := by ring
        rw [h_zero] at h_det
        exact h_det rfl
      change (if M.c = 0 then none else some (M.a / M.c)) = some z'
      rw [if_neg hc]
      congr 1
      have h_eq : M.a = M.c * z' := by
        calc M.a = (-M.c * z' + M.a) + M.c * z' := by ring
        _ = 0 + M.c * z' := by rw [h_inv_denom]
        _ = M.c * z' := by ring
      rw [h_eq]
      have : M.c * z' / M.c = z' * M.c / M.c := by rw [mul_comm]
      rw [this, mul_div_cancel_right₀ _ hc]
    · rw [if_neg h_inv_denom]
      change (if M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d = 0 then none else some _) = some z'
      have h_denom : M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d ≠ 0 := by
        intro h_zero
        have h_det := M.det_ne_zero
        have h_zero_mul : (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) = 0 := by
          rw [h_zero, zero_mul]
        have h_simp : (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) = M.a * M.d - M.b * M.c := by
          calc (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a)
            _ = M.c * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) * (-M.c * z' + M.a)) + M.d * (-M.c * z' + M.a) := by ring
            _ = M.c * (M.d * z' + -M.b) + M.d * (-M.c * z' + M.a) := by
              rw [div_mul_cancel₀ _ h_inv_denom]
            _ = M.a * M.d - M.b * M.c := by ring
        rw [h_simp] at h_zero_mul
        exact h_det h_zero_mul
      rw [if_neg h_denom]
      congr 1
      have h_cross : (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) = z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) := by
        have h1 : (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) * (-M.c * z' + M.a) = (M.a * M.d - M.b * M.c) * z' := by
          calc (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) * (-M.c * z' + M.a)
            _ = M.a * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) * (-M.c * z' + M.a)) + M.b * (-M.c * z' + M.a) := by ring
            _ = M.a * (M.d * z' + -M.b) + M.b * (-M.c * z' + M.a) := by rw [div_mul_cancel₀ _ h_inv_denom]
            _ = (M.a * M.d - M.b * M.c) * z' := by ring
        have h2 : z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) = (M.a * M.d - M.b * M.c) * z' := by
          calc z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a)
            _ = z' * ((M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a)) := by ring
            _ = z' * (M.c * (((M.d * z' + -M.b) / (-M.c * z' + M.a)) * (-M.c * z' + M.a)) + M.d * (-M.c * z' + M.a)) := by ring
            _ = z' * (M.c * (M.d * z' + -M.b) + M.d * (-M.c * z' + M.a)) := by rw [div_mul_cancel₀ _ h_inv_denom]
            _ = (M.a * M.d - M.b * M.c) * z' := by ring
        have h3 : (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) * (-M.c * z' + M.a) = z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) * (-M.c * z' + M.a) := by
          rw [h1, h2]
        exact mul_right_cancel₀ h_inv_denom h3
      calc (M.a * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.b) / (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d)
        _ = (z' * (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d)) / (M.c * ((M.d * z' + -M.b) / (-M.c * z' + M.a)) + M.d) := by rw [h_cross]
        _ = z' := by rw [mul_div_cancel_right₀ _ h_denom]

lemma eval_inv_left (M : MobiusTransform) (z : RiemannSphere) :
    (inv M).eval (M.eval z) = z := by
  simpa [inv] using (eval_inv (inv M) z)

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
        have num_eq : (M1.a * M2.a + M1.b * M2.c) = M1.a * M2.a := by rw [h2c, mul_zero, add_zero]
        have den_eq : (M1.c * M2.a + M1.d * M2.c) = M1.c * M2.a := by rw [h2c, mul_zero, add_zero]
        rw [num_eq, den_eq]
        have cross : M1.a * M2.a / (M1.c * M2.a) = M1.a / M1.c := by
          rw [eq_div_iff_mul_eq h1c]
          calc M1.a * M2.a / (M1.c * M2.a) * M1.c
            _ = M1.a * M2.a * M1.c / (M1.c * M2.a) := by rw [div_mul_eq_mul_div]
            _ = M1.a * (M1.c * M2.a) / (M1.c * M2.a) := by ring_nf
            _ = M1.a := by rw [mul_div_cancel_right₀ _ (mul_ne_zero h1c h2a)]
        rw [cross]
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

end InfoGeometry.Topology.MobiusRecoveredHelpers
