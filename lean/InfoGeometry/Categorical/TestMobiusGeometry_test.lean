
import Mathlib.Data.Complex.Basic

open Complex

namespace InfoGeometry

def RiemannSphere := Option ℂ

structure MobiusTransform where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

namespace MobiusTransform

noncomputable def eval (M : MobiusTransform) (z : RiemannSphere) : RiemannSphere :=
  match z with
  | none => if M.c = 0 then none else some (M.a / M.c)
  | some z' =>
      let denom := M.c * z' + M.d
      if denom = 0 then none else some ((M.a * z' + M.b) / denom)

def equiv (M1 M2 : MobiusTransform) : Prop :=
  ∀ z : RiemannSphere, M1.eval z = M2.eval z

end MobiusTransform

theorem pgl_equivalence (M : MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) :
    let M_scaled : MobiusTransform := {
      a := lam * M.a,
      b := lam * M.b,
      c := lam * M.c,
      d := lam * M.d,
      det_ne_zero := by
        dsimp
        have h1 : lam * M.a * (lam * M.d) - lam * M.b * (lam * M.c) = lam^2 * (M.a * M.d - M.b * M.c) := by ring
        rw [h1]
        have hl2 : lam^2 ≠ 0 := pow_ne_zero 2 hlam
        exact mul_ne_zero hl2 M.det_ne_zero
    };
    ∀ z, M.eval z = M_scaled.eval z := by
  intro M_scaled z
  cases z with
  | none =>
    dsimp [MobiusTransform.eval, M_scaled]
    have hc : M.c = 0 ↔ lam * M.c = 0 := by
      constructor
      · intro h; rw [h, mul_zero]
      · intro h
        cases mul_eq_zero.mp h with
        | inl h1 => exact False.elim (hlam h1)
        | inr h2 => exact h2
    by_cases h : M.c = 0
    · rw [if_pos h, if_pos (hc.mp h)]
    · rw [if_neg h, if_neg (hc.not.mp h)]
      have eq1 : lam * M.a / (lam * M.c) = M.a / M.c := mul_div_mul_left M.a M.c hlam
      rw [eq1]
  | some z' =>
    dsimp [MobiusTransform.eval, M_scaled]
    have hd : M.c * z' + M.d = 0 ↔ lam * M.c * z' + lam * M.d = 0 := by
      constructor
      · intro h
        have h2 : lam * (M.c * z' + M.d) = lam * 0 := by rw [h]
        rw [mul_zero] at h2
        have h3 : lam * (M.c * z') + lam * M.d = 0 := by
          calc lam * (M.c * z') + lam * M.d = lam * (M.c * z' + M.d) := by ring
          _ = 0 := h2
        have h4 : lam * M.c * z' + lam * M.d = 0 := by
          calc lam * M.c * z' + lam * M.d = lam * (M.c * z') + lam * M.d := by ring
          _ = 0 := h3
        exact h4
      · intro h
        have h2 : lam * (M.c * z' + M.d) = 0 := by
          calc lam * (M.c * z' + M.d) = lam * M.c * z' + lam * M.d := by ring
          _ = 0 := h
        cases mul_eq_zero.mp h2 with
        | inl h1 => exact False.elim (hlam h1)
        | inr h2 => exact h2
    by_cases h : M.c * z' + M.d = 0
    · rw [if_pos h, if_pos (hd.mp h)]
    · rw [if_neg h, if_neg (hd.not.mp h)]
      have hnum : lam * M.a * z' + lam * M.b = lam * (M.a * z' + M.b) := by ring
      have hden : lam * M.c * z' + lam * M.d = lam * (M.c * z' + M.d) := by ring
      rw [hnum, hden]
      have eq2 : lam * (M.a * z' + M.b) / (lam * (M.c * z' + M.d)) = (M.a * z' + M.b) / (M.c * z' + M.d) := mul_div_mul_left (M.a * z' + M.b) (M.c * z' + M.d) hlam
      rw [eq2]
