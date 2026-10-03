import Mathlib.Order.Basic
import Mathlib.Order.Interval.Set.Basic

namespace InfoGeometry.Topology.CausalDiamondIntervalPosetBridge

variable (P : Type*) [PartialOrder P]

/-- The type of valid intervals [a, b] where a ≤ b, representing causal diamonds. -/
structure CausalDiamond where
  bot : P
  top : P
  le_bound : bot ≤ top

namespace CausalDiamond

/-- The information order on causal diamonds (reverse inclusion):
[a, b] ⊑ [c, d] iff [c, d] ⊆ [a, b] iff a ≤ c and d ≤ b.
This is exactly the interval domain information order. -/
instance : PartialOrder (CausalDiamond P) where
  le x y := x.bot ≤ y.bot ∧ y.top ≤ x.top
  le_refl x := ⟨le_refl _, le_refl _⟩
  le_trans x y z h1 h2 := ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩
  le_antisymm x y h1 h2 := by
    obtain ⟨hx1, hx2⟩ := h1
    obtain ⟨hy1, hy2⟩ := h2
    have h_bot : x.bot = y.bot := le_antisymm hx1 hy1
    have h_top : x.top = y.top := le_antisymm hy2 hx2
    cases x; cases y; congr

/-- The embedding of the interval domain into P × P^op -/
def toDoubledPoset (x : CausalDiamond P) : P × OrderDual P :=
  (x.bot, OrderDual.toDual x.top)

/-- The embedding is order-preserving. -/
theorem toDoubledPoset_monotone : Monotone (toDoubledPoset P) := by
  intro x y h
  exact h

/-- The embedding reflects the order (so it is an order embedding). -/
theorem toDoubledPoset_reflects_le {x y : CausalDiamond P} :
    toDoubledPoset P x ≤ toDoubledPoset P y → x ≤ y := by
  intro h
  exact h

/-- The embedding is injective. -/
theorem toDoubledPoset_injective : Function.Injective (toDoubledPoset P) := by
  intro x y h
  have h_le1 : toDoubledPoset P x ≤ toDoubledPoset P y := le_of_eq h
  have h_le2 : toDoubledPoset P y ≤ toDoubledPoset P x := le_of_eq h.symm
  exact le_antisymm (toDoubledPoset_reflects_le P h_le1) (toDoubledPoset_reflects_le P h_le2)

/-- Alexandrov interval boundedness: the set of elements in the causal diamond
is exactly the intersection of the future of the bottom and the past of the top. -/
def elements (x : CausalDiamond P) : Set P :=
  { p | x.bot ≤ p ∧ p ≤ x.top }

theorem elements_eq_inter (x : CausalDiamond P) :
    x.elements = Set.Ici x.bot ∩ Set.Iic x.top := rfl

end CausalDiamond
end InfoGeometry.Topology.CausalDiamondIntervalPosetBridge
