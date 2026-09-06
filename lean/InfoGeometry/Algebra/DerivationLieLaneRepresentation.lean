import InfoGeometry.Algebra.DerivationLieLane
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Operator representation carried by a derivation Lie lane

A `DerivationLieLane` already stores a faithful Lie action by bundled
nonassociative derivations.  This file exposes the same action as a native
Mathlib Lie homomorphism into `Module.End`.

The two exported identities are the exact representation and Leibniz laws:

* `ρ([x,y]) a = ρ(x) (ρ(y) a) - ρ(y) (ρ(x) a)`;
* `ρ(x) (a*b) = ρ(x) a * b + a * ρ(x) b`.

They are the algebraic input for the derivation-based Chevalley--Eilenberg
complex.
-/

namespace InfoGeometry.Algebra.DerivationLieLane

variable {R A : Type*}
variable [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

variable (K : InfoGeometry.Algebra.DerivationLieLane R A)

/-- The underlying operator action bundled as a native Mathlib Lie homomorphism. -/
def operatorActionLieHom : K.L →ₗ⁅R⁆ Module.End R A :=
  { K.operatorAction with
    map_lie' := by
      intro x y
      simpa [operatorAction, NonAssocDerivation.lie_apply] using
        congrArg (fun D : NonAssocDerivation.derivations R A =>
          (D : Module.End R A)) (K.act_map_lie x y) }

/-- Evaluation of the bundled operator representation. -/
@[simp] theorem operatorActionLieHom_apply (x : K.L) (a : A) :
    K.operatorActionLieHom x a = K.operatorAction x a := by
  simp [operatorActionLieHom, operatorAction]

/-- Pointwise representation law for the derivation action. -/
theorem operatorAction_commutator_apply (x y : K.L) (a : A) :
    K.operatorAction ⁅x, y⁆ a =
      K.operatorAction x (K.operatorAction y a) -
        K.operatorAction y (K.operatorAction x a) := by
  have h := congrArg (fun T : Module.End R A => T a)
    (K.operatorAction_map_lie x y)
  simpa [LieRing.of_associative_ring_bracket, Module.End.mul_apply] using h

/-- Every represented Lie generator acts by the native Leibniz rule. -/
theorem operatorAction_leibniz (x : K.L) (a b : A) :
    K.operatorAction x (a * b) =
      K.operatorAction x a * b + a * K.operatorAction x b := by
  simpa [DerivationLieLane.operatorAction_apply] using
    (InfoGeometry.Algebra.NonAssocDerivation.derivations_leibniz
      (K.act x) a b)

end InfoGeometry.Algebra.DerivationLieLane
