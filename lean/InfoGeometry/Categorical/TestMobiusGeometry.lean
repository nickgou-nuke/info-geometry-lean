import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Basic

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
  unfold MobiusTransform.eval
  dsimp
  cases z with
  | none =>
    by_cases hc : M.c = 0
    · have hcs : lam * M.c = 0 := by rw [hc, mul_zero]
      rw [if_pos hc, if_pos hcs]
    · have hcs : lam * M.c ≠ 0 := mul_ne_zero hlam hc
      rw [if_neg hc, if_neg hcs]
      have : lam * M.a / (lam * M.c) = M.a / M.c := by
        rw [mul_div_mul_left M.a M.c hlam]
      rw [this]
  | some z' =>
    by_cases hdenom : M.c * z' + M.d = 0
    · have hdenom_scaled : lam * M.c * z' + lam * M.d = 0 := by
        calc lam * M.c * z' + lam * M.d = lam * (M.c * z' + M.d) := by ring
        _ = lam * 0 := by rw [hdenom]
        _ = 0 := mul_zero lam
      rw [if_pos hdenom, if_pos hdenom_scaled]
    · have hdenom_scaled : lam * M.c * z' + lam * M.d ≠ 0 := by
        intro h
        have : lam * (M.c * z' + M.d) = 0 := by
          calc lam * (M.c * z' + M.d) = lam * M.c * z' + lam * M.d := by ring
          _ = 0 := h
        cases mul_eq_zero.mp this with
        | inl h1 => exact hlam h1
        | inr h2 => exact hdenom h2
      rw [if_neg hdenom, if_neg hdenom_scaled]
      congr 2
      calc (lam * M.a * z' + lam * M.b) / (lam * M.c * z' + lam * M.d)
        _ = (lam * (M.a * z' + M.b)) / (lam * (M.c * z' + M.d)) := by ring
        _ = (M.a * z' + M.b) / (M.c * z' + M.d) := by
          rw [mul_div_mul_left (M.a * z' + M.b) (M.c * z' + M.d) hlam]
