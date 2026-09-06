import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

namespace InfoGeometry.Topology.PointedGroups

/-- The category of pointed groups (A, a_0) where a_0 : A -/
structure PointedGroup where
  carrier : Type
  grp : Group carrier
  pt : carrier

/-- Structural representation of the amalgamated sum (free product) of groups -/
structure FreeProductData where
  ProdType : Type → Type → Type
  grp : ∀ A B [Group A] [Group B], Group (ProdType A B)
  inl : ∀ A B [Group A] [Group B], A →* ProdType A B
  inr : ∀ A B [Group A] [Group B], B →* ProdType A B

/-- Tensor product (Coproduct) of pointed groups -/
def tensor (D : FreeProductData) (A B : PointedGroup) : PointedGroup :=
  letI := A.grp
  letI := B.grp
  letI := D.grp A.carrier B.carrier
  { carrier := D.ProdType A.carrier B.carrier
    grp := D.grp A.carrier B.carrier
    pt := D.inl A.carrier B.carrier A.pt * D.inr A.carrier B.carrier B.pt }

/-- The braiding operator acting on elements.
c_{A,B}(a) = b_0 a b_0^{-1}
c_{A,B}(b) = b
-/
def braiding_action_A (D : FreeProductData) (A B : PointedGroup) (a : A.carrier) : D.ProdType B.carrier A.carrier :=
  letI := A.grp
  letI := B.grp
  letI := D.grp B.carrier A.carrier
  let b_0 := D.inl B.carrier A.carrier B.pt
  let a_embedded := D.inr B.carrier A.carrier a
  b_0 * a_embedded * b_0⁻¹

def braiding_action_B (D : FreeProductData) (A B : PointedGroup) (b : B.carrier) : D.ProdType B.carrier A.carrier :=
  letI := A.grp
  letI := B.grp
  letI := D.grp B.carrier A.carrier
  D.inl B.carrier A.carrier b

/-- Readout theorem for Street's `A`-side pointed-group braiding action. -/
theorem braiding_action_A_readout
    (D : FreeProductData) (A B : PointedGroup) (a : A.carrier) :
    braiding_action_A D A B a =
      letI := A.grp
      letI := B.grp
      letI := D.grp B.carrier A.carrier
      let b₀ := D.inl B.carrier A.carrier B.pt
      let a' := D.inr B.carrier A.carrier a
      b₀ * a' * b₀⁻¹ := by
  rfl

/-- Readout theorem for Street's `B`-side pointed-group braiding action. -/
theorem braiding_action_B_readout
    (D : FreeProductData) (A B : PointedGroup) (b : B.carrier) :
    braiding_action_B D A B b =
      letI := A.grp
      letI := B.grp
      letI := D.grp B.carrier A.carrier
      D.inl B.carrier A.carrier b := by
  rfl

/-- Abstract group-level form of the conjugating half of Street's braiding. -/
def conjugatingBraidAction {G : Type} [Group G] (base x : G) : G :=
  base * x * base⁻¹

/-- The conjugating braid action sends the identity to the identity. -/
theorem conjugatingBraidAction_one {G : Type} [Group G] (base : G) :
    conjugatingBraidAction base 1 = 1 := by
  simp [conjugatingBraidAction]

/-- The conjugating braid action preserves multiplication. -/
theorem conjugatingBraidAction_mul {G : Type} [Group G] (base x y : G) :
    conjugatingBraidAction base (x * y) =
      conjugatingBraidAction base x * conjugatingBraidAction base y := by
  simp [conjugatingBraidAction]

/-- The conjugating braid action is invertible by conjugation with the inverse base. -/
theorem conjugatingBraidAction_inverse_cancel {G : Type} [Group G] (base x : G) :
    conjugatingBraidAction base⁻¹ (conjugatingBraidAction base x) = x := by
  simp [conjugatingBraidAction]
  group

/-- A theorem-safe packet for finite pointed-group braid witnesses. -/
structure PointedGroupBraidWitness (Carrier : Type) [Group Carrier] where
  base : Carrier
  x : Carrier
  y : Carrier

namespace PointedGroupBraidWitness

variable {Carrier : Type} [Group Carrier]
variable (W : PointedGroupBraidWitness Carrier)

/-- The `A`-side action is conjugation by the pointed element. -/
def actionX : Carrier :=
  conjugatingBraidAction W.base W.x

/-- The `B`-side action fixes the right input in the abstract group readout. -/
def actionY : Carrier :=
  W.y

/-- The abstract `A`-side action unfolds to the conjugation formula. -/
theorem actionX_readout : W.actionX = W.base * W.x * W.base⁻¹ := by
  rfl

/-- The abstract `B`-side action is the identity readout on the right input. -/
theorem actionY_readout : W.actionY = W.y := by
  rfl

end PointedGroupBraidWitness

end InfoGeometry.Topology.PointedGroups
