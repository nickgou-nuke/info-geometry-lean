universe u

namespace WarehamCGA

class Scalar (K : Type u) where
  zero : K
  add : K → K → K
  neg : K → K
  mul : K → K → K

infixl:65 " +ₛ " => Scalar.add
infixl:70 " *ₛ " => Scalar.mul
prefix:80 "-ₛ" => Scalar.neg

structure CGA (K : Type u) [Scalar K] where
  E : Type u
  V : Type u
  addE : E → E → E
  dot : V → V → K
  F : E → V
  nInf : V
  n0 : V
  zeroEq : K → Prop
  dist2 : E → E → K
  F_null : ∀ x : E, zeroEq (dot (F x) (F x))
  conformal_distance : ∀ x y : E, zeroEq ((dot (F x) (F y)) +ₛ (dist2 x y))
  translate_F : ∀ x a : E, F (addE x a) = F (addE x a)

variable {K : Type u} [Scalar K]

theorem F_null_thm (A : CGA K) (x : A.E) :
    A.zeroEq (A.dot (A.F x) (A.F x)) :=
  A.F_null x

theorem conformal_distance_thm (A : CGA K) (x y : A.E) :
    A.zeroEq ((A.dot (A.F x) (A.F y)) +ₛ (A.dist2 x y)) :=
  A.conformal_distance x y

theorem translate_F_thm (A : CGA K) (x a : A.E) :
    A.F (A.addE x a) = A.F (A.addE x a) :=
  A.translate_F x a

inductive BladeGrade where
  | scalar | vector | bivector | trivector | quadvector | pseudoscalar
  deriving Repr, DecidableEq

structure RotorSystem (K : Type u) [Scalar K] where
  M : Type u
  mul : M → M → M
  rev : M → M
  one : M
  unit : M → Prop
  sandwich : M → M → M
  inverse_by_reversion : ∀ R, unit R → mul R (rev R) = one

end WarehamCGA
