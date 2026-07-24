import Mathlib.Algebra.BigOperators.Ring.Finset
import InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge
import InfoGeometry.SuperMetriplectic.WeylCharacter

open scoped BigOperators

/-!
# Weyl Character Cantor Bridge

The old fake vacuous surface is replaced by finite-stage theorem content.  A
Weyl/Gibbs packet can be indexed by the finite binary words `BitWord n` from
the Cantor/UHF owner, and the Cantor owner supplies the finite cylinder atom
readout at a boundary point.

No analytic Cantor limit or global Weyl-character theorem is claimed here.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.WeylCharacterCantorBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/--
Finite-stage Weyl partition readout over binary Cantor words.

This is exactly the owner theorem from
`InfoGeometry.SuperMetriplectic.WeylCharacter`, specialized to `BitWord n`.
-/
theorem bitword_partitionFunction_eq_weighted_sum
    (n : ℕ)
    (W : WeylCharacterGibbsPacket (BitWord n)) :
    W.partitionFunction = ∑ w : BitWord n, W.degeneracy w * W.gibbsFactor w :=
  W.partitionFunction_eq_weighted_sum

/--
The Cantor boundary atom at the finite prefix evaluates to one.

This is exactly the finite-cylinder owner theorem from
`UHFBooleanProjectionCantorBridge`.
-/
theorem boundary_prefix_atom_eval_one
    (n : ℕ)
    (x : CantorBoundary) :
    cylinder n (atomProjection n (boundaryPrefix n x)) x = 1 :=
  cylinder_atom_boundaryPrefix_self n x

/--
Finite Weyl/Cantor bridge packet: the Weyl partition is a sum over binary
words, and the boundary prefix selects its cylinder atom.
-/
theorem bitword_weyl_partition_and_boundary_atom
    (n : ℕ)
    (W : WeylCharacterGibbsPacket (BitWord n))
    (x : CantorBoundary) :
    W.partitionFunction = ∑ w : BitWord n, W.degeneracy w * W.gibbsFactor w ∧
      cylinder n (atomProjection n (boundaryPrefix n x)) x = 1 :=
  ⟨bitword_partitionFunction_eq_weighted_sum n W, boundary_prefix_atom_eval_one n x⟩

end InfoGeometry.GrandUnification.WeylCharacterCantorBridge

end noncomputable section
