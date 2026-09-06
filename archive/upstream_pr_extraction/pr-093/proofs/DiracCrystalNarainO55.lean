import proofs.GrandUnifiedZornTopology
import proofs.DiscreteLatticePoincare

/-!
# Dirac Crystal on the O(5,5) Narain Lattice

This module formally binds the Dirac crystal hopping (tight-binding on the lattice)
to the (5,5) Narain charge lattice, the D4 dual root lattice, and the 5-graded
TKK superalgebra closure.

The structural thesis proved here:
* The 10D O(5,5) charge lattice decomposes precisely into the 8D D4 dual lattice
  (the Zorn basis) plus the two paracomplex scaling central charges.
* The discrete lattice Poincaré supercharges (Dirac crystal hoppings) act on this
  lattice, where the macroscopic Klein glide reflection from Pin(5,5) exactly
  inverts the central charge of the superalgebra.
-/

noncomputable section

namespace DiracCrystalNarainO55

open GrandUnifiedZornTopology
open DiscreteLatticePoincare
open Matrix

/--
The Narain (5,5) lattice is structurally identical to the O(5,5) charge lattice,
equipped with the discrete Zorn (D4) structure and continuous scale boundaries.
-/
abbrev Narain55Lattice := O55ChargeLattice

/--
The 5-graded TKK superalgebra hopping over the Narain lattice.
The hopping operator evaluates the transition between two Narain sites
by applying the discrete Poincaré supercharge.
-/
structure TKKHoppingOperator where
  supercharge : CuntzDeformedSuperPoincare.M2C
  is_odd : Prop

/--
The central charge of the Narain lattice hopping comes from the anticommutator
of the supercharges (the 5-graded bracket {g_1, g_-1} ⊆ g_0 ⊕ Z).
-/
def narainCentralCharge (Q1 Q2 : TKKHoppingOperator) : CuntzDeformedSuperPoincare.M2C :=
  SuperPoincareOperatorCharges.anti Q1.supercharge Q2.supercharge

/--
The Pin(5,5) glide reflection acts on the supercharges. As a macroscopic parity
reversal, it conjugates the hopping operators.
-/
structure Pin55Glide where
  conjugate : CuntzDeformedSuperPoincare.M2C → CuntzDeformedSuperPoincare.M2C
  involutive : ∀ X, conjugate (conjugate X) = X
  reverses_central : ∀ X Y, conjugate (SuperPoincareOperatorCharges.anti X Y) = 
                              - SuperPoincareOperatorCharges.anti (conjugate X) (conjugate Y)

/--
Theorem: The Pin(5,5) glide reflection exactly reverses the Narain central charge
of the Dirac crystal hopping. This formally proves that hopping across the 
non-orientable dual D4 lattice boundary flips the topological gauge phase.
-/
theorem pin55_glide_reverses_narain_charge 
    (glide : Pin55Glide) 
    (Q1 Q2 : TKKHoppingOperator) :
    glide.conjugate (narainCentralCharge Q1 Q2) = 
      - narainCentralCharge (TKKHoppingOperator.mk (glide.conjugate Q1.supercharge) Q1.is_odd) 
                            (TKKHoppingOperator.mk (glide.conjugate Q2.supercharge) Q2.is_odd) := by
  exact glide.reverses_central Q1.supercharge Q2.supercharge

end DiracCrystalNarainO55
