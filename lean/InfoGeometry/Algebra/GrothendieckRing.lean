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

/-- The canonical map into the multiplicative Grothendieck completion. -/
def grothendieckRingHom : M →+* Grothendieck M where
  toFun := grothendieckMap M
  map_one' := grothendieckMap_one
  map_mul' := grothendieckMap_mul
  map_zero' := (grothendieckMap M).map_zero
  map_add' := (grothendieckMap M).map_add

theorem grothendieckFunctor_map_mul
    {N : Type u} [CommSemiring N] (f : M →+* N)
    (x y : Grothendieck M) :
    grothendieckFunctor f.toAddMonoidHom (x * y) =
      grothendieckFunctor f.toAddMonoidHom x *
        grothendieckFunctor f.toAddMonoidHom y := by
  refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid M)
    (s₂ := grothendieckSetoid M) x y ?_
  intro a b
  dsimp [grothendieckMul, grothendieckFunctor, grothendieckLift,
    grothendieckMap]
  apply Quotient.sound
  use 0
  simp [map_add, map_mul]
  ring

def grothendieckRingMap
    {N : Type u} [CommSemiring N] (f : M →+* N) :
    Grothendieck M →+* Grothendieck N where
  toFun := grothendieckFunctor f.toAddMonoidHom
  map_one' := by
    rw [← grothendieckMap_one (M := M)]
    simpa [grothendieckMap] using
      grothendieckFunctor_mk f.toAddMonoidHom (1, 0)
  map_mul' := grothendieckFunctor_map_mul f
  map_zero' := (grothendieckFunctor f.toAddMonoidHom).map_zero
  map_add' := (grothendieckFunctor f.toAddMonoidHom).map_add

@[simp]
theorem grothendieckRingMap_apply_canonical
    {N : Type u} [CommSemiring N] (f : M →+* N) (m : M) :
    grothendieckRingMap f (grothendieckMap M m) =
      grothendieckMap N (f m) := by
  simpa [grothendieckMap] using
    grothendieckFunctor_mk f.toAddMonoidHom (m, 0)

theorem ringHom_ext_of_grothendieckMap
    {A : Type*} [CommRing A]
    {F G : Grothendieck M →+* A}
    (h : ∀ m, F (grothendieckMap M m) = G (grothendieckMap M m)) : F = G := by
  apply RingHom.ext
  intro x
  rcases grothendieck_eq_sub x with ⟨a, b, rfl⟩
  rw [map_sub, map_sub, h a, h b]

@[simp]
theorem grothendieckRingMap_id (M : Type u) [CommSemiring M] :
    grothendieckRingMap (RingHom.id M) = RingHom.id (Grothendieck M) := by
  apply ringHom_ext_of_grothendieckMap
  intro m
  rw [grothendieckRingMap_apply_canonical]
  rfl

@[simp]
theorem grothendieckRingMap_comp
    {N P : Type u} [CommSemiring N] [CommSemiring P]
    (f : M →+* N) (g : N →+* P) :
    grothendieckRingMap (g.comp f) =
      (grothendieckRingMap g).comp (grothendieckRingMap f) := by
  apply ringHom_ext_of_grothendieckMap
  intro m
  simp [RingHom.comp_apply, grothendieckRingMap_apply_canonical]

noncomputable def grothendieckRingLift
    {A : Type*} [CommRing A] (f : M →+* A) :
    Grothendieck M →+* A where
  toFun := grothendieckLift f.toAddMonoidHom
  map_one' := by
    rw [← grothendieckMap_one (M := M)]
    change grothendieckLift f.toAddMonoidHom (grothendieckMap M 1) = 1
    rw [grothendieckLift_comp]
    change f 1 = 1
    rw [f.map_one]
  map_mul' := by
    intro x y
    refine Quotient.inductionOn₂ (s₁ := grothendieckSetoid M)
      (s₂ := grothendieckSetoid M) x y ?_
    intro a b
    dsimp [grothendieckMul, grothendieckLift, grothendieckMap]
    change (f (a.1 * b.1 + a.2 * b.2) -
        f (a.1 * b.2 + a.2 * b.1)) = _
    simp only [map_add, map_mul]
    ring
  map_zero' := (grothendieckLift f.toAddMonoidHom).map_zero
  map_add' := (grothendieckLift f.toAddMonoidHom).map_add

@[simp]
theorem grothendieckRingLift_apply
    {A : Type*} [CommRing A] (f : M →+* A) (m : M) :
    grothendieckRingLift f (grothendieckMap M m) = f m := by
  exact grothendieckLift_comp f.toAddMonoidHom m

theorem grothendieckRingHom_lift_exists
    {A : Type*} [CommRing A] (f : M →+* A) :
    ∃ F : Grothendieck M →+* A,
      ∀ m, F (grothendieckMap M m) = f m := by
  exact ⟨grothendieckRingLift f, grothendieckRingLift_apply f⟩

theorem grothendieckRingLift_unique
    {A : Type*} [CommRing A] (f : M →+* A)
    (F : Grothendieck M →+* A)
    (hF : ∀ m, F (grothendieckMap M m) = f m) :
    F = grothendieckRingLift f := by
  apply ringHom_ext_of_grothendieckMap
  intro m
  rw [hF, grothendieckRingLift_apply]

theorem grothendieckRingHom_lift_unique
    {A : Type*} [CommRing A] (f : M →+* A)
    (F G : Grothendieck M →+* A)
    (hF : ∀ m, F (grothendieckMap M m) = f m)
    (hG : ∀ m, G (grothendieckMap M m) = f m) : F = G := by
  rw [grothendieckRingLift_unique f F hF,
    grothendieckRingLift_unique f G hG]

theorem grothendieckRingHom_injective_of_cancellation
    (h_cancel : IsCancellationMonoid M) :
    Function.Injective (grothendieckRingHom : M →+* Grothendieck M) := by
  intro x y hxy
  apply grothendieckMap_injective_of_cancellation h_cancel
  exact hxy

end InfoGeometry.Algebra.GrothendieckRing
