import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Derivation-level Lie lanes

The carrier of a Jordan, Zorn, or split-octonion model is not itself the TKK
Lie algebra.  Its canonical Lie object is the native subalgebra of linear
endomorphisms satisfying the Leibniz rule.  This file provides the small
interface used to place concrete lanes at that operator level.

No dimension or physical interpretation is built into this interface.  In
particular, a derivation lane may be a proper subalgebra of a larger TKK or
orthogonal realization; an embedding is not silently promoted to an
equivalence.
-/

namespace InfoGeometry.Algebra

/-! ## Lie actions on modules

This lane is intentionally weaker than `DerivationLieLane`: a Lie action on a
module does not require the module to carry an ambient multiplication.  This
is the canonical interface for the native non-associative Zorn carrier.
-/

structure LieActionLane (R A : Type*) [CommRing R]
    [AddCommGroup A] [Module R A] where
  L : Type*
  lieRing : LieRing L
  lieAlgebra : LieAlgebra R L
  act : L →ₗ⁅R⁆ Module.End R A

attribute [instance] LieActionLane.lieRing LieActionLane.lieAlgebra

namespace LieActionLane

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
variable (K : LieActionLane R A)

abbrev operatorAction : K.L →ₗ[R] Module.End R A := K.act.toLinearMap

@[simp] theorem operatorAction_apply (x : K.L) (a : A) :
    K.operatorAction x a = (K.act x : Module.End R A) a := rfl

theorem operatorAction_commutator_apply (x y : K.L) (a : A) :
    K.operatorAction ⁅x, y⁆ a = K.operatorAction x (K.operatorAction y a) -
      K.operatorAction y (K.operatorAction x a) := by
  have h := K.act.map_lie x y
  exact congrArg (fun T : Module.End R A => T a) h

end LieActionLane

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- A Lie lane whose operators act as derivations of a nonassociative carrier. -/
structure DerivationLieLane (R A : Type*) [CommRing R]
    [NonUnitalNonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] where
  L : Type*
  lieRing : LieRing L
  lieAlgebra : LieAlgebra R L
  act : L →ₗ⁅R⁆ NonAssocDerivation.derivations R A
  faithful : Function.Injective act

attribute [instance] DerivationLieLane.lieRing DerivationLieLane.lieAlgebra

namespace DerivationLieLane

variable (K : DerivationLieLane R A)

@[simp] theorem act_map_lie (x y : K.L) :
    K.act ⁅x, y⁆ = ⁅K.act x, K.act y⁆ :=
  K.act.map_lie x y

theorem act_injective : Function.Injective K.act := K.faithful

/-- The induced action on the underlying carrier, exposing the actual
operator representation without unbundling the derivation proof. -/
def operatorAction : K.L →ₗ[R] Module.End R A :=
  { toFun := fun x => (K.act x : Module.End R A)
    map_add' := by intro x y; exact congrArg Subtype.val (K.act.toLinearMap.map_add x y)
    map_smul' := by intro r x; exact congrArg Subtype.val (K.act.toLinearMap.map_smul r x) }

@[simp] theorem operatorAction_apply (x : K.L) (a : A) :
    K.operatorAction x a = (K.act x : Module.End R A) a := by
  change ((K.act x : NonAssocDerivation.derivations R A) : Module.End R A) a = _
  rfl

theorem operatorAction_map_lie (x y : K.L) :
    K.operatorAction ⁅x, y⁆ =
      ⁅K.operatorAction x, K.operatorAction y⁆ := by
  simpa [operatorAction, NonAssocDerivation.lie_apply] using
    congrArg (fun D : NonAssocDerivation.derivations R A =>
      (D : Module.End R A)) (K.act_map_lie x y)

end DerivationLieLane

/-- An equivariant identification of two derivation lanes on the same carrier.
The Lie equivalence is the algebraic interchangeability witness; the second
field says that both presentations have the same operator action. -/
structure DerivationLaneEquiv (K₁ K₂ : DerivationLieLane R A) where
  map : K₁.L ≃ₗ⁅R⁆ K₂.L
  equivariant : ∀ x, K₂.act (map x) = K₁.act x

namespace DerivationLaneEquiv

variable {K₁ K₂ K₃ : DerivationLieLane R A}

@[simp] theorem operatorAction_eq (e : DerivationLaneEquiv K₁ K₂) (x : K₁.L) :
    K₂.operatorAction (e.map x) = K₁.operatorAction x := by
  simpa [DerivationLieLane.operatorAction] using congrArg (fun D : NonAssocDerivation.derivations R A =>
    (D : Module.End R A)) (e.equivariant x)

def refl (K : DerivationLieLane R A) : DerivationLaneEquiv K K where
  map := LieEquiv.refl
  equivariant _ := rfl

def trans (e₁₂ : DerivationLaneEquiv K₁ K₂)
    (e₂₃ : DerivationLaneEquiv K₂ K₃) : DerivationLaneEquiv K₁ K₃ where
  map := e₁₂.map.trans e₂₃.map
  equivariant x := by
    change K₃.act (e₂₃.map (e₁₂.map x)) = K₁.act x
    rw [e₂₃.equivariant, e₁₂.equivariant]

end DerivationLaneEquiv

end InfoGeometry.Algebra
