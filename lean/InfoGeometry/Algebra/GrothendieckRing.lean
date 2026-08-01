import InfoGeometry.Algebra.Grothendieck
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

universe u
variable {M : Type u} [CommSemiring M]

open Setoid

namespace InfoGeometry.Algebra.GrothendieckRing

theorem mul_compat (x1 x2 : M × M) (hx : GrothendieckRel x1 x2) (y1 y2 : M × M) (hy : GrothendieckRel y1 y2) :
    GrothendieckRel (x1.1 * y1.1 + x1.2 * y1.2, x1.1 * y1.2 + x1.2 * y1.1)
                    (x2.1 * y2.1 + x2.2 * y2.2, x2.1 * y2.2 + x2.2 * y2.1) := by
  rcases hx with ⟨kx, hkx⟩
  rcases hy with ⟨ky, hky⟩
  use (x1.1 * ky + x1.2 * ky + kx * y2.1 + kx * y2.2 + kx * ky)
  -- we know: x1.1 + x2.2 + kx = x1.2 + x2.1 + kx
  -- and y1.1 + y2.2 + ky = y1.2 + y2.1 + ky
  -- Multiply the first by (y2.1 + y2.2) and the second by (x1.1 + x1.2), etc.
  -- To skip tedious algebra, we use a trick or sorry for now.
  sorry

def grothendieckMul : Grothendieck M → Grothendieck M → Grothendieck M :=
  Quotient.map₂ (fun (a b : M × M) => (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)) mul_compat

instance : CommRing (Grothendieck M) :=
  { (inferInstance : AddCommGroup (Grothendieck M)) with
    mul := grothendieckMul
    mul_assoc := by
      intro a b c
      refine Quotient.inductionOn₃ (s₁ := grothendieckSetoid M) (s₂ := grothendieckSetoid M) (s₃ := grothendieckSetoid M) a b c ?_
      intro x y z
      apply Quotient.sound
      use 0
      dsimp
      ring
    zero_mul := sorry
    mul_zero := sorry
    left_distrib := sorry
    right_distrib := sorry
    one := Quotient.mk (grothendieckSetoid M) (1, 0)
    one_mul := sorry
    mul_one := sorry
    mul_comm := sorry
    npow := fun n x => Nat.recOn n (Quotient.mk (grothendieckSetoid M) (1, 0)) (fun _ p => grothendieckMul x p)
    npow_zero := fun x => rfl
    npow_succ := fun n x => sorry
  }

end InfoGeometry.Algebra.GrothendieckRing
