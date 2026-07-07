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
    ∀ z, M.eval z = M_scaled.eval z := by sorry
