import InfoGeometry.Topology.MobiusGeometry

/-!
# MobiusHelpers

Small importable packet for Möbius composition and inverse evaluation.
-/

namespace InfoGeometry

open Complex

/-- The inverse Möbius transform. -/
def mobiusInv (M : MobiusTransform) : MobiusTransform :=
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
def mobiusComp (M1 M2 : MobiusTransform) : MobiusTransform :=
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

/-- The inverse Möbius transform evaluates as a left inverse for `eval`. -/
lemma mobius_eval_inv (M : MobiusTransform) (z : RiemannSphere) :
    M.eval ((mobiusInv M).eval z) = z := by
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

/-- Composition/evaluation compatibility target.

The explicit `Option ℂ` evaluator requires a separate denominator and
pole-transport proof for the finite and infinite branches. Keep the intended
equation as an open proposition until that native proof is available. -/
def mobius_eval_comp (M1 M2 : MobiusTransform) (z : RiemannSphere) : Prop :=
  (mobiusComp M1 M2).eval z = M1.eval (M2.eval z)
