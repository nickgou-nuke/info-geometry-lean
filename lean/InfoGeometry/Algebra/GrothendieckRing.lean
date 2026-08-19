import InfoGeometry.Algebra.Grothendieck
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

universe u
variable {M : Type u} [CommSemiring M]

open Setoid

namespace InfoGeometry.Algebra.GrothendieckRing

theorem mul_left_compat (x1 x2 : M × M) (hx : GrothendieckRel x1 x2)
    (y : M × M) :
    GrothendieckRel
      (x1.1 * y.1 + x1.2 * y.2, x1.1 * y.2 + x1.2 * y.1)
      (x2.1 * y.1 + x2.2 * y.2, x2.1 * y.2 + x2.2 * y.1) := by
  rcases hx with ⟨kx, hkx⟩
  use kx * y.1 + kx * y.2
  calc
    (x1.1 * y.1 + x1.2 * y.2) +
        (x2.1 * y.2 + x2.2 * y.1) +
        (kx * y.1 + kx * y.2) =
      (x1.1 + x2.2 + kx) * y.1 +
        (x1.2 + x2.1 + kx) * y.2 := by ring
    _ = (x1.2 + x2.1 + kx) * y.1 +
        (x1.1 + x2.2 + kx) * y.2 := by rw [hkx]
    _ = (x1.1 * y.2 + x1.2 * y.1) +
        (x2.1 * y.1 + x2.2 * y.2) +
        (kx * y.1 + kx * y.2) := by ring

theorem mul_right_compat (x : M × M) (y1 y2 : M × M)
    (hy : GrothendieckRel y1 y2) :
    GrothendieckRel
      (x.1 * y1.1 + x.2 * y1.2, x.1 * y1.2 + x.2 * y1.1)
      (x.1 * y2.1 + x.2 * y2.2, x.1 * y2.2 + x.2 * y2.1) := by
  rcases hy with ⟨ky, hky⟩
  use x.1 * ky + x.2 * ky
  calc
    (x.1 * y1.1 + x.2 * y1.2) +
        (x.1 * y2.2 + x.2 * y2.1) +
        (x.1 * ky + x.2 * ky) =
      x.1 * (y1.1 + y2.2 + ky) +
        x.2 * (y1.2 + y2.1 + ky) := by ring
    _ = x.1 * (y1.2 + y2.1 + ky) +
        x.2 * (y1.1 + y2.2 + ky) := by rw [hky]
    _ = (x.1 * y1.2 + x.2 * y1.1) +
        (x.1 * y2.1 + x.2 * y2.2) +
        (x.1 * ky + x.2 * ky) := by ring

theorem mul_compat (x1 x2 : M × M) (hx : GrothendieckRel x1 x2)
    (y1 y2 : M × M) (hy : GrothendieckRel y1 y2) :
    GrothendieckRel
      (x1.1 * y1.1 + x1.2 * y1.2, x1.1 * y1.2 + x1.2 * y1.1)
      (x2.1 * y2.1 + x2.2 * y2.2, x2.1 * y2.2 + x2.2 * y2.1) :=
  grothendieck_trans (mul_left_compat x1 x2 hx y1)
    (mul_right_compat x2 y1 y2 hy)

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
    zero_mul := by
      intro a
      refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
      intro x
      apply Quotient.sound
      use 0
      ring
    mul_zero := by
      intro a
      refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
      intro x
      apply Quotient.sound
      use 0
    left_distrib := by
      intro a b c
      refine Quotient.inductionOn₃ (s₁ := grothendieckSetoid M)
        (s₂ := grothendieckSetoid M) (s₃ := grothendieckSetoid M) a b c ?_
      intro x y z
      apply Quotient.sound
      use 0
      dsimp [grothendieckMul, grothendieckAdd]
      ring
    right_distrib := by
      intro a b c
      refine Quotient.inductionOn₃ (s₁ := grothendieckSetoid M)
        (s₂ := grothendieckSetoid M) (s₃ := grothendieckSetoid M) a b c ?_
      intro x y z
      apply Quotient.sound
      use 0
      dsimp [grothendieckMul, grothendieckAdd]
      ring
    one := Quotient.mk (grothendieckSetoid M) (1, 0)
    one_mul := by
      intro a
      refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
      intro x
      apply Quotient.sound
      use 0
      dsimp [grothendieckMul]
      ring
    mul_one := by
      intro a
      refine Quotient.inductionOn (s := grothendieckSetoid M) a ?_
      intro x
      apply Quotient.sound
      use 0
      dsimp [grothendieckMul]
      ring
    mul_comm := by
      intro a b
      refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid M)
        (s₂ := grothendieckSetoid M) a b ?_
      intro x y
      apply Quotient.sound
      use 0
      dsimp [grothendieckMul]
      ring
    npow := fun n x => Nat.recOn n (Quotient.mk (grothendieckSetoid M) (1, 0))
      (fun _ p => grothendieckMul p x)
    npow_zero := fun x => rfl
    npow_succ := fun n x => rfl
  }

@[simp]
theorem grothendieckMap_one :
    grothendieckMap M 1 = (1 : Grothendieck M) := by
  apply Quotient.sound
  use 0
  simp [add_comm]

@[simp]
theorem grothendieckMap_mul (x y : M) :
    grothendieckMap M (x * y) =
      grothendieckMap M x * grothendieckMap M y := by
  apply Quotient.sound
  use 0
  dsimp [grothendieckMap, grothendieckMul]
  simp

end InfoGeometry.Algebra.GrothendieckRing
