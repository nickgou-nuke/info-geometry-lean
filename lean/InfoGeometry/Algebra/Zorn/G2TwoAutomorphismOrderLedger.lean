import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite order ledger for `G₂(2)` automorphism claims

This file records the finite arithmetic facts checked by
`tools/sympy/g2two_automorphism_order_ledger.py` using GAP/Atlas.

It repairs the order-level part of the statement:

* `|G₂(2)| = 12096`;
* `|G₂(2)'| = 6048` and the index is `2`;
* `|Aut(G₂(2))| = 12096` and the outer automorphism quotient has order `1` in
  the Atlas model;
* over `𝔽₃`, `|PGL₃(3)| = |PSL₃(3)| = 5616`, so a group of order `5616` cannot
  be the same finite group as the `12096`-element `G₂(2)`/`Aut(G₂(2))` object.

This is only an order ledger.  It does not construct any finite group carrier or
prove an isomorphism/classification theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger

/-- GAP/Atlas order of `G₂(2)`. -/
def g2TwoOrder : ℕ := 12096

/-- GAP/Atlas order of the derived subgroup `G₂(2)'`. -/
def g2TwoDerivedOrder : ℕ := 6048

/-- GAP/Atlas index `[G₂(2):G₂(2)']`. -/
def g2TwoDerivedIndex : ℕ := 2

/-- GAP/Atlas order of `Aut(G₂(2))`. -/
def autG2TwoOrder : ℕ := 12096

/-- GAP/Atlas outer automorphism quotient order for `G₂(2)`. -/
def outG2TwoOrder : ℕ := 1

/-- Over `𝔽₃`, field automorphisms are trivial, and `|PGL₃(3)| = 5616`. -/
def pgl3F3Order : ℕ := 5616

/-- Over `𝔽₃`, `|PSL₃(3)| = 5616`. -/
def psl3F3Order : ℕ := 5616

/-- The derived subgroup has half the order of `G₂(2)`. -/
theorem g2Two_derived_index_order :
    g2TwoDerivedOrder * g2TwoDerivedIndex = g2TwoOrder := by
  norm_num [g2TwoDerivedOrder, g2TwoDerivedIndex, g2TwoOrder]

/-- The Atlas automorphism-group order agrees with the `G₂(2)` order. -/
theorem autG2TwoOrder_eq_g2TwoOrder : autG2TwoOrder = g2TwoOrder := by
  rfl

/-- The outer automorphism quotient is order one in the GAP/Atlas check. -/
theorem outG2TwoOrder_eq_one : outG2TwoOrder = 1 := by
  rfl

/-- `PGL₃(3)` and `PSL₃(3)` have the same order in this finite ledger. -/
theorem pgl3F3Order_eq_psl3F3Order : pgl3F3Order = psl3F3Order := by
  rfl

/-- Order mismatch: `PGL₃(3)` over `𝔽₃` is not the `12096`-element `G₂(2)`. -/
theorem pgl3F3Order_ne_g2TwoOrder : pgl3F3Order ≠ g2TwoOrder := by
  norm_num [pgl3F3Order, g2TwoOrder]

/-- Order mismatch: `PΣL₃(3)` with trivial field automorphism order cannot be `G₂(2)`. -/
theorem pSigmaL3F3_order_ne_g2TwoOrder
    (pSigmaOrder : ℕ)
    (h : pSigmaOrder = pgl3F3Order) :
    pSigmaOrder ≠ g2TwoOrder := by
  rw [h]
  exact pgl3F3Order_ne_g2TwoOrder

/-- Consolidated corrected finite order packet. -/
theorem corrected_g2two_automorphism_order_packet :
    g2TwoOrder = 12096 ∧
      g2TwoDerivedOrder = 6048 ∧
      g2TwoDerivedIndex = 2 ∧
      autG2TwoOrder = 12096 ∧
      outG2TwoOrder = 1 ∧
      pgl3F3Order = 5616 ∧
      pgl3F3Order ≠ g2TwoOrder := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, pgl3F3Order_ne_g2TwoOrder⟩

end InfoGeometry.Algebra.Zorn.G2TwoAutomorphismOrderLedger
