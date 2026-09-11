import InfoGeometry.Categorical.InductivePosetColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ProofDAGRepresentationBridge
import InfoGeometry.Canonical.CausalFunctor
import InfoGeometry.Projective.Twistor.Incidence

/-!
# Penrose poset/category foundation

This file packages the repo's existing foundational spine for discrete causal /
incidence models:

* a partial order is viewed both as a preorder category and as a proof DAG;
* forward/backward cones are read directly from the order relation;
* categorical cocones/colimits over preorder-valued diagrams are upper
  bounds / least upper bounds;
* Penrose-style twistor incidence is a scale-invariant relation that can be
  propagated along the order;
* causal functors out of the poset preserve information along arrows.

The file is intentionally thin: it does not construct a concrete Penrose
spin-network, AF limit, or twistor field equation. It only exposes the
foundational category/poset/incidence surfaces already proved elsewhere in the
repo and in mathlib.
-/

namespace InfoGeometry.Canonical.PenrosePosetCategoryFoundation

open CategoryTheory
open CategoryTheory.Limits
open Set
open InfoGeometry.Categorical.InductivePosetColimit
open InfoGeometry.Canonical.ProofDAGRepresentationBridge
open InfoGeometry.Projective.Twistor

universe u v uJ

section PosetToProofDAG

variable {α : Type u} [PartialOrder α]

/-- Any partial order determines a proof-DAG by reading `a ≤ b` as causal reachability. -/
def proofDAGOfPartialOrder : ProofDAG α where
  le := (· ≤ ·)
  refl := fun _ => le_rfl
  trans := fun {_ _ _} hab hbc => le_trans hab hbc
  antisymm := fun {_ _} hab hba => le_antisymm hab hba

@[simp] theorem forwardCone_eq_order_upper
    (a : α) :
    InfoGeometry.Causal.ProofDAGRepresentation.forwardCone
        (proofDAGOfPartialOrder (α := α)) a = {b | a ≤ b} :=
  rfl

@[simp] theorem backwardCone_eq_order_lower
    (a : α) :
    InfoGeometry.Causal.ProofDAGRepresentation.backwardCone
        (proofDAGOfPartialOrder (α := α)) a = {b | b ≤ a} :=
  rfl

@[simp] theorem mem_forwardCone_iff_le
    {a b : α} :
    b ∈ InfoGeometry.Causal.ProofDAGRepresentation.forwardCone
          (proofDAGOfPartialOrder (α := α)) a ↔ a ≤ b :=
  Iff.rfl

@[simp] theorem mem_backwardCone_iff_le
    {a b : α} :
    b ∈ InfoGeometry.Causal.ProofDAGRepresentation.backwardCone
          (proofDAGOfPartialOrder (α := α)) a ↔ b ≤ a :=
  Iff.rfl

 theorem order_cones_intersect_self
    (a b : α)
    (hab : b ∈ InfoGeometry.Causal.ProofDAGRepresentation.forwardCone
        (proofDAGOfPartialOrder (α := α)) a)
    (hba : b ∈ InfoGeometry.Causal.ProofDAGRepresentation.backwardCone
        (proofDAGOfPartialOrder (α := α)) a) :
    b = a :=
  cones_intersect_self (proofDAGOfPartialOrder (α := α)) a b ⟨hab, hba⟩

end PosetToProofDAG

section PreorderCategoricalCones

variable {J : Type uJ} [Category.{v} J]
variable {P : Type u} [Preorder P]

/-- In a preorder category, an upper bound packages directly as a cocone. -/
def preorderCoconeOfUpperBound
    (F : J ⥤ P) {ub : P}
    (hub : ub ∈ upperBounds (range F.obj)) :
    Cocone F :=
  coconeOfUpperBound F hub

/-- In a preorder category, a least upper bound packages directly as a colimit cocone. -/
def preorderColimitCoconeOfIsLUB
    (F : J ⥤ P) {sup : P}
    (h_lub : IsLUB (range F.obj) sup) :
    ColimitCocone F :=
  colimitCoconeOfIsLUB F h_lub

 theorem preorder_colimit_le_of_upperBound
    (F : J ⥤ P) {sup ub : P}
    (h_lub : IsLUB (range F.obj) sup)
    (hub : ub ∈ upperBounds (range F.obj)) :
    sup ≤ ub :=
  colimit_le_of_upperBound F h_lub hub

end PreorderCategoricalCones

section OrderedTwistorIncidence

variable {α : Type u} [Preorder α]
variable {𝕜 T D : Type u}
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

/--
A discrete Penrose incidence field over an ordered event set: whenever `a ≤ b`,
the dual twistor attached to `a` is incident with the twistor attached to `b`.
-/
def IncidenceAlongOrder
    (I : TwistorIncidenceDatum 𝕜 T D)
    (Z : α → T)
    (Ξ : α → D) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → I.Incidence (Ξ a) (Z b)

 theorem incidenceAlongOrder_of_le
    {I : TwistorIncidenceDatum 𝕜 T D}
    {Z : α → T} {Ξ : α → D}
    (hI : IncidenceAlongOrder I Z Ξ)
    {a b : α} (hab : a ≤ b) :
    I.Incidence (Ξ a) (Z b) :=
  hI hab

 theorem incidenceAlongOrder_dualScale
    (I : TwistorIncidenceDatum 𝕜 T D)
    (u : 𝕜ˣ)
    {Z : α → T} {Ξ : α → D}
    (hI : IncidenceAlongOrder I Z Ξ) :
    IncidenceAlongOrder I Z (fun a => I.dualScale u (Ξ a)) := by
  intro a b hab
  exact (I.incidence_scale_left u (Ξ a) (Z b)).2 (hI hab)

 theorem incidenceAlongOrder_twistorScale
    (I : TwistorIncidenceDatum 𝕜 T D)
    (u : 𝕜ˣ)
    {Z : α → T} {Ξ : α → D}
    (hI : IncidenceAlongOrder I Z Ξ) :
    IncidenceAlongOrder I (fun a => I.twScale u (Z a)) Ξ := by
  intro a b hab
  exact (I.incidence_scale_right u (Ξ a) (Z b)).2 (hI hab)

end OrderedTwistorIncidence

section CausalFunctorReadout

variable {α : Type u} [PartialOrder α]

 theorem causal_information_conservation_of_le
    (F : CausalFunctor α) [HasColimit F]
    {a b : α} (hab : a ≤ b)
    (x : F.obj a) :
    (colimit.ι F a) x = (colimit.ι F b) ((F.map (homOfLE hab)) x) :=
  causal_information_conservation F hab x

end CausalFunctorReadout

end InfoGeometry.Canonical.PenrosePosetCategoryFoundation
