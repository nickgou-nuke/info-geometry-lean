import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Dependent products of groups

The old `arrow_group` module uses pointed loop spaces to put a group
structure on dependent maps.  The algebraic core is the ordinary pointwise
group on a dependent function type; Mathlib already supplies that instance.
This file ports its reusable pointwise homomorphism interface without making
claims about loop-space truncations.
-/

namespace InfoGeometry.Spectral.Algebra.ArrowGroup

universe u v w

variable {A : Type u} {B : A → Type v} {C : A → Type w}
variable [∀ a, Group (B a)] [∀ a, Group (C a)]

abbrev Carrier (B : A → Type v) := ∀ a, B a

def pointwiseInv (f : Carrier B) : Carrier B := fun a => (f a)⁻¹

def pointwiseMul (f g : Carrier B) : Carrier B := fun a => f a * g a

@[simp] theorem pointwiseMul_apply (f g : Carrier B) (a : A) :
    pointwiseMul f g a = f a * g a := rfl

@[simp] theorem pointwiseInv_apply (f : Carrier B) (a : A) :
    pointwiseInv f a = (f a)⁻¹ := rfl

theorem pointwise_mul_assoc (f g h : Carrier B) :
    pointwiseMul (pointwiseMul f g) h = pointwiseMul f (pointwiseMul g h) := by
  funext a
  simp [pointwiseMul, mul_assoc]

theorem pointwise_mul_left_inv (f : Carrier B) :
    pointwiseMul (pointwiseInv f) f = 1 := by
  funext a
  simp [pointwiseMul, pointwiseInv]

def map (f : ∀ a, B a →* C a) : Carrier B →* Carrier C where
  toFun x a := f a (x a)
  map_one' := by
    funext a
    simp
  map_mul' x y := by
    funext a
    simp

@[simp] theorem map_apply (f : ∀ a, B a →* C a) (x : Carrier B) (a : A) :
    map f x a = f a (x a) := rfl

@[simp] theorem map_id (x : Carrier B) :
    map (fun _ => MonoidHom.id _) x = x := by
  funext a
  rfl

def evaluation (a : A) : Carrier B →* B a where
  toFun f := f a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem evaluation_apply (a : A) (f : Carrier B) :
    evaluation a f = f a := rfl

end InfoGeometry.Spectral.Algebra.ArrowGroup
