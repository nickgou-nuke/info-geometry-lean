import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

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

/-- Concrete instantiation of MobiusTransform -/
def id : MobiusTransform := {
  a := 1,
  b := 0,
  c := 0,
  d := 1,
  det_ne_zero := by norm_num
}

noncomputable def eval (M : MobiusTransform) (z : RiemannSphere) : RiemannSphere :=
  match z with
  | none => if M.c = 0 then none else some (M.a / M.c)
  | some z' =>
      let denom := M.c * z' + M.d
      if denom = 0 then none else some ((M.a * z' + M.b) / denom)

def equiv (M1 M2 : MobiusTransform) : Prop :=
  ∀ z : RiemannSphere, M1.eval z = M2.eval z

end MobiusTransform

def scaledTransform (M : MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) : MobiusTransform := {
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
}

lemma pgl_equivalence_none (M : MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) :
    M.eval none = (scaledTransform M lam hlam).eval none := by
  change (if M.c = 0 then none else some (M.a / M.c)) = (if lam * M.c = 0 then none else some (lam * M.a / (lam * M.c)))
  by_cases hc : M.c = 0
  · have hcs : lam * M.c = 0 := by rw [hc, mul_zero]
    rw [if_pos hc, if_pos hcs]
  · have hcs : lam * M.c ≠ 0 := mul_ne_zero hlam hc
    rw [if_neg hc, if_neg hcs]
    have : lam * M.a / (lam * M.c) = M.a / M.c := by
      rw [mul_div_mul_left M.a M.c hlam]
    rw [this]

lemma pgl_equivalence_some (M : MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) (z' : ℂ) :
    M.eval (some z') = (scaledTransform M lam hlam).eval (some z') := by
  change (if M.c * z' + M.d = 0 then none else some ((M.a * z' + M.b) / (M.c * z' + M.d))) =
    (if lam * M.c * z' + lam * M.d = 0 then none else some ((lam * M.a * z' + lam * M.b) / (lam * M.c * z' + lam * M.d)))
  by_cases hdenom : M.c * z' + M.d = 0
  · have hdenom_scaled : lam * M.c * z' + lam * M.d = 0 := by
      have h_ring : lam * M.c * z' + lam * M.d = lam * (M.c * z' + M.d) := by ring
      rw [h_ring, hdenom, mul_zero]
    rw [if_pos hdenom, if_pos hdenom_scaled]
  · have hdenom_scaled : lam * M.c * z' + lam * M.d ≠ 0 := by
      intro h
      have ht : lam * (M.c * z' + M.d) = 0 := by
        have h1 : lam * (M.c * z' + M.d) = lam * M.c * z' + lam * M.d := by ring
        rw [h1, h]
      cases mul_eq_zero.mp ht with
      | inl h1 => exact hlam h1
      | inr h2 => exact hdenom h2
    rw [if_neg hdenom, if_neg hdenom_scaled]
    have hnum : lam * M.a * z' + lam * M.b = lam * (M.a * z' + M.b) := by ring
    have hden : lam * M.c * z' + lam * M.d = lam * (M.c * z' + M.d) := by ring
    rw [hnum, hden]
    simpa using (mul_div_mul_left (M.a * z' + M.b) (M.c * z' + M.d) hlam).symm

theorem pgl_equivalence (M : MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) :
    ∀ z, M.eval z = (scaledTransform M lam hlam).eval z := by
  intro z
  cases z with
  | none => exact pgl_equivalence_none M lam hlam
  | some z' => exact pgl_equivalence_some M lam hlam z'

end InfoGeometry
