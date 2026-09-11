import Mathlib.Algebra.Group.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Tactic

namespace InfoGeometry.Topology.PointedGroups

/-- The category of pointed groups (A, a_0) where a_0 : A -/
structure PointedGroup where
  carrier : GrpCat
  pt : carrier

/-- Coproduct of pointed groups, owned by Mathlib's group free product. -/
def tensor (A B : PointedGroup) : PointedGroup :=
  { carrier := GrpCat.of (Monoid.Coprod A.carrier B.carrier)
    pt := Monoid.Coprod.inl A.pt * Monoid.Coprod.inr B.pt }

/-- The braiding operator acting on elements.
c_{A,B}(a) = b_0 a b_0^{-1}
c_{A,B}(b) = b
-/
def braiding_action_A
    (A B : PointedGroup) (a : A.carrier) :
    Monoid.Coprod B.carrier A.carrier :=
  let b_0 := Monoid.Coprod.inl B.pt
  let a_embedded := Monoid.Coprod.inr a
  b_0 * a_embedded * b_0⁻¹

def braiding_action_B
    (A B : PointedGroup) (b : B.carrier) :
    Monoid.Coprod B.carrier A.carrier :=
  Monoid.Coprod.inl b

/-- Abstract group-level form of the conjugating half of Street's braiding. -/
def conjugatingBraidAction {G : Type} [Group G] (base x : G) : G :=
  base * x * base⁻¹

/-- Native group-automorphism owner of the conjugating pointed braid action. -/
def conjugatingBraidAutomorphism {G : Type} [Group G] (base : G) : G ≃* G :=
  MulAut.conj base

/-- The elementwise action is evaluation of its native automorphism owner. -/
theorem conjugatingBraidAutomorphism_apply {G : Type} [Group G] (base x : G) :
    conjugatingBraidAutomorphism base x = conjugatingBraidAction base x := by
  exact MulAut.conj_apply base x

/-- The conjugating braid action sends the identity to the identity. -/
theorem conjugatingBraidAction_one {G : Type} [Group G] (base : G) :
    conjugatingBraidAction base 1 = 1 := by
  rw [← conjugatingBraidAutomorphism_apply]
  exact map_one (conjugatingBraidAutomorphism base)

/-- The conjugating braid action preserves multiplication. -/
theorem conjugatingBraidAction_mul {G : Type} [Group G] (base x y : G) :
    conjugatingBraidAction base (x * y) =
      conjugatingBraidAction base x * conjugatingBraidAction base y := by
  rw [← conjugatingBraidAutomorphism_apply,
    ← conjugatingBraidAutomorphism_apply,
    ← conjugatingBraidAutomorphism_apply]
  exact map_mul (conjugatingBraidAutomorphism base) x y

/-- The conjugating braid action is invertible by conjugation with the inverse base. -/
theorem conjugatingBraidAction_inverse_cancel {G : Type} [Group G] (base x : G) :
    conjugatingBraidAction base⁻¹ (conjugatingBraidAction base x) = x := by
  simp [conjugatingBraidAction, mul_assoc]

/-- The `A`-side action is conjugation by the pointed element. -/
def pointedBraidActionX
    {Carrier : Type} [Group Carrier] (base x : Carrier) : Carrier :=
  conjugatingBraidAction base x

/-- The `B`-side action fixes the right input in the abstract group readout. -/
def pointedBraidActionY
    {Carrier : Type} [Group Carrier] (y : Carrier) : Carrier :=
  y

@[simp]
theorem pointedBraidActionX_one
    {Carrier : Type} [Group Carrier] (base : Carrier) :
    pointedBraidActionX base 1 = 1 :=
  conjugatingBraidAction_one base

theorem pointedBraidActionX_mul
    {Carrier : Type} [Group Carrier] (base x y : Carrier) :
    pointedBraidActionX base (x * y) =
      pointedBraidActionX base x * pointedBraidActionX base y :=
  conjugatingBraidAction_mul base x y

@[simp]
theorem pointedBraidActionX_inverse_cancel
    {Carrier : Type} [Group Carrier] (base x : Carrier) :
    pointedBraidActionX base⁻¹ (pointedBraidActionX base x) = x :=
  conjugatingBraidAction_inverse_cancel base x

@[simp]
theorem pointedBraidActionY_eq
    {Carrier : Type} [Group Carrier] (y : Carrier) :
    pointedBraidActionY y = y :=
  rfl

/-! ## Bundled pointed braid inputs -/

/--
Bundled inputs for the two elementwise pointed-group braid actions.

This restores the historical public carrier without storing coherence as
evidence: the nontrivial action is owned by the native automorphism
`MulAut.conj`, while `base`, `x`, and `y` are genuine group data.
-/
def PointedGroupBraidWitness (Carrier : Type) [Group Carrier] :=
  Carrier × Carrier × Carrier

namespace PointedGroupBraidWitness

variable {Carrier : Type} [Group Carrier]
variable (W : PointedGroupBraidWitness Carrier)

def base : Carrier := W.1

def x : Carrier := W.2.1

def y : Carrier := W.2.2

def mk (base x y : Carrier) : PointedGroupBraidWitness Carrier :=
  (base, x, y)

/-- The bundled `A`-side action, evaluated through the native conjugation owner. -/
def actionX : Carrier :=
  pointedBraidActionX W.base W.x

/-- The bundled `B`-side action, which fixes the right input. -/
def actionY : Carrier :=
  pointedBraidActionY W.y

/-- The bundled `A`-side action is conjugation by the pointed base element. -/
theorem actionX_eq :
    W.actionX = conjugatingBraidAction W.base W.x :=
  rfl

@[simp]
theorem actionY_eq :
    W.actionY = W.y :=
  rfl

end PointedGroupBraidWitness

end InfoGeometry.Topology.PointedGroups
