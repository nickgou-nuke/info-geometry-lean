import Mathlib.Tactic

/-!
# Finite `G₂(2)` automorphism order ledger

This module is the Lean companion to
`tools/sympy/g2two_automorphism_order_ledger.py`.

It records only exact natural-number order facts verified externally by
GAP/AtlasRep/CTblLib and by the SymPy arithmetic ledger:

* finite Atlas/Chevalley `G2(2)` has order `12096` and is identified by GAP's
  character-table library as `U3(3).2`;
* its derived subgroup `G2(2)'` has order `6048` and is identified as `U3(3)`;
* the true order-compatible unitary extension `Aut(PSU₃(3))` has order `12096`;
* `PΓL₃(3)=PGL₃(3)=PSL₃(3)` has order `5616`, since `F₃` is a prime field;
* therefore the naive order-level identification of finite `G2(2)` with
  `PΓL₃(3)` is impossible.

Honesty boundary: arithmetic order inequalities do not by themselves prove any
group isomorphism or the real split-octonion Lie-group theorem
`Aut(𝕆_s)=G_{2(2)}`.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger

/-- GAP/Atlas finite `G2(2)` / `U3(3).2` order. -/
def g2TwoOrder : ℕ := 12096

/-- GAP/Atlas finite `G2(2)'` / `U3(3)` order. -/
def g2TwoDerivedOrder : ℕ := 6048

/-- GAP `PSU(3,3)` order; same order as the finite `G2(2)'` simple core. -/
def psu3F3Order : ℕ := 6048

/-- GAP `Aut(PSU(3,3))` order; the order-compatible unitary extension. -/
def pgammaU3F3Order : ℕ := 12096

/-- `|GL₃(F₃)| = (3^3-1)(3^3-3)(3^3-3^2)`. -/
def gl3F3Order : ℕ := 11232

/-- `|PSL₃(F₃)|`; here this equals `|PGL₃(F₃)|` by order. -/
def psl3F3Order : ℕ := 5616

/-- `|PGL₃(F₃)| = |GL₃(F₃)| / |F₃^×| = 11232 / 2`. -/
def pgl3F3Order : ℕ := 5616

/-- `F₃` has no nontrivial field automorphism, so `PΓL₃(3)` has the same order as `PGL₃(3)`. -/
abbrev pgammaL3F3Order : ℕ := pgl3F3Order

/-- The finite `G2(2)` group is an index-two extension of its derived subgroup at the order level. -/
theorem g2Two_derived_index_order : g2TwoDerivedOrder * 2 = g2TwoOrder := by
  norm_num [g2TwoDerivedOrder, g2TwoOrder]

/-- The GAP `PSU(3,3)` order matches the finite `G2(2)'` order ledger. -/
theorem psu3F3Order_eq_g2TwoDerivedOrder : psu3F3Order = g2TwoDerivedOrder := by
  norm_num [psu3F3Order, g2TwoDerivedOrder]

/-- The true unitary extension has the finite `G2(2)` order. -/
theorem pgammaU3F3Order_eq_g2TwoOrder : pgammaU3F3Order = g2TwoOrder := by
  norm_num [pgammaU3F3Order, g2TwoOrder]

/-- The true unitary extension is an index-two extension of the `PSU(3,3)` core by order. -/
theorem psu3F3Order_unitary_extension_index : psu3F3Order * 2 = pgammaU3F3Order := by
  norm_num [psu3F3Order, pgammaU3F3Order]

/-- Direct arithmetic formula for `|GL₃(F₃)|`. -/
theorem gl3F3_order_formula :
    gl3F3Order = (3 ^ 3 - 1) * (3 ^ 3 - 3) * (3 ^ 3 - 3 ^ 2) := by
  norm_num [gl3F3Order]

/-- Direct arithmetic formula for `|PGL₃(F₃)|`. -/
theorem pgl3F3_order_formula : pgl3F3Order * 2 = gl3F3Order := by
  norm_num [pgl3F3Order, gl3F3Order]

/-- In this order ledger, `PSL₃(F₃)` and `PGL₃(F₃)` have the same order. -/
theorem psl3F3_order_eq_pgl3F3_order : psl3F3Order = pgl3F3Order := by
  norm_num [psl3F3Order, pgl3F3Order]

/-- Since `F₃` is prime, the order ledger has `|PΓL₃(3)| = |PGL₃(3)|`. -/
theorem pgammaL3F3_order_eq_pgl3F3_order : pgammaL3F3Order = pgl3F3Order := by
  norm_num [pgammaL3F3Order, pgl3F3Order]

/-- Certified order mismatch: finite `G2(2)` is not order-compatible with `PΓL₃(3)`. -/
theorem pgammaL3F3Order_ne_g2TwoOrder : pgammaL3F3Order ≠ g2TwoOrder := by
  norm_num [pgammaL3F3Order, pgl3F3Order, g2TwoOrder]

/-- Equivalent order mismatch using the `PGL₃(3)` spelling. -/
theorem pgl3F3Order_ne_g2TwoOrder : pgl3F3Order ≠ g2TwoOrder := by
  norm_num [pgl3F3Order, g2TwoOrder]

/-- The finite Atlas `G2(2)'` order matches the `U3(3)` simple core order recorded by GAP. -/
theorem g2TwoDerivedOrder_double_eq_g2TwoOrder :
    g2TwoDerivedOrder + g2TwoDerivedOrder = g2TwoOrder := by
  norm_num [g2TwoDerivedOrder, g2TwoOrder]

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismOrderLedger
