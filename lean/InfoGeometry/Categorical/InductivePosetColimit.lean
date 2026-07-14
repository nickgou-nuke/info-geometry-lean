import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Order.Zorn

/-!
# Inductive Posets as Preorder Categories

This file records the theorem-safe categorical/order bridge used by the
repository's Zorn and tower lanes.

Mathlib already installs a category instance on every preorder.  We therefore
do not define a custom `Category P` instance.  The categorical content is the
standard preorder-category dictionary:

* a morphism `x ⟶ y` is the same data as `x ≤ y`;
* a cocone over a diagram is an upper bound of its object range;
* a colimit cocone over a preorder category is a least upper bound.

The Zorn statement below is the order-theoretic maximality theorem that follows
from the chain-upper-bound condition.
-/

namespace InductivePosetColimit

open CategoryTheory
open CategoryTheory.Limits
open Set

universe v uJ uP

/-- An inductive preorder: every chain has an upper bound. -/
def IsInductivePoset (P : Type uP) [Preorder P] : Prop :=
  ∀ c : Set P, IsChain (· ≤ ·) c → BddAbove c

/--
Zorn maximality from the inductive-poset condition, with a maximal element above
the chosen seed.

This is the precise order-theoretic form of “every inductive poset category has
a maximal object”.  It delegates to mathlib's Zorn theorem on the upset
`Ici a`.
-/
theorem zorn_maximal_above
    {P : Type uP} [Preorder P]
    (h_inductive : IsInductivePoset P)
    (a : P) :
    ∃ m : P, a ≤ m ∧ IsMax m := by
  exact zorn_le_nonempty_Ici₀ a
    (fun c _hc_subset h_chain _y _hy => h_inductive c h_chain)
    a le_rfl

/--
Partial-order readout of `zorn_maximal_above`, matching the usual equality
form of maximality.
-/
theorem zorn_maximal_above_eq
    {P : Type uP} [PartialOrder P]
    (h_inductive : IsInductivePoset P)
    (a : P) :
    ∃ m : P, a ≤ m ∧ ∀ x : P, m ≤ x → x = m := by
  rcases zorn_maximal_above h_inductive a with ⟨m, ham, hm⟩
  exact ⟨m, ham, fun x hmx => le_antisymm (hm hmx) hmx⟩

/-- In a preorder category, the canonical morphism attached to an inequality. -/
def poset_hom_of_le
    {P : Type uP} [Preorder P] {x y : P}
    (hxy : x ≤ y) :
    x ⟶ y :=
  homOfLE hxy

theorem poset_hom_of_le_eq_homOfLE
    {P : Type uP} [Preorder P] {x y : P}
    (hxy : x ≤ y) :
    poset_hom_of_le hxy = homOfLE hxy :=
  rfl

/-- In a preorder category, every morphism reads back to an inequality. -/
theorem le_of_poset_hom
    {P : Type uP} [Preorder P] {x y : P}
    (f : x ⟶ y) :
    x ≤ y :=
  leOfHom f

/-- A categorical cocone over a preorder-valued diagram is exactly an upper bound. -/
def coconeOfUpperBound
    {J : Type uJ} [Category.{v} J]
    {P : Type uP} [Preorder P]
    (F : J ⥤ P) {ub : P}
    (hub : ub ∈ upperBounds (range F.obj)) :
    Cocone F :=
  Preorder.coconeOfUpperBound F hub

/--
A least upper bound of the object range of a preorder-valued diagram gives a
colimit cocone.  This is the categorical form of `colim D = sup C`.
-/
def colimitCoconeOfIsLUB
    {J : Type uJ} [Category.{v} J]
    {P : Type uP} [Preorder P]
    (F : J ⥤ P) {sup : P}
    (h_lub : IsLUB (range F.obj) sup) :
    ColimitCocone F :=
  Preorder.colimitCoconeOfIsLUB F h_lub

/--
Read back the universal property of a preorder colimit as the least-upper-bound
inequality: every competing upper bound receives the unique morphism from the
colimit point.
-/
theorem colimit_le_of_upperBound
    {J : Type uJ} [Category.{v} J]
    {P : Type uP} [Preorder P]
    (F : J ⥤ P) {sup ub : P}
    (h_lub : IsLUB (range F.obj) sup)
    (hub : ub ∈ upperBounds (range F.obj)) :
    sup ≤ ub :=
  h_lub.2 hub

end InductivePosetColimit
