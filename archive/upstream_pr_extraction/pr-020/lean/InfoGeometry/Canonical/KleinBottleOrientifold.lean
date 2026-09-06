import InfoGeometry.Canonical.PrimeGasMaxEnt
import InfoGeometry.Clifford.HestenesDirac
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.KleinBottleOrientifold

Topological orientifold packet for the prime-gas lane.

The purpose of this module is not to prove that the Klein bottle literally
creates the Möbius function.  The purpose is to package, in a kernel-safe way,
the precise hypotheses one needs to represent:

- a `V4` Weyl quotient,
- an orientation-reversing filter,
- a fermion-parity projection,
- and the square-killing support condition that singles out square-free
  occupancy patterns.

Those claims remain explicit hypotheses until a concrete geometric/Fock model
instantiates them.
-/

namespace InfoGeometry.Canonical.KleinBottleOrientifold

open InfoGeometry.Canonical.PrimeGasMaxEnt
open InfoGeometry.Clifford.HestenesDirac

universe u

set_option linter.dupNamespace false in
/--
Abstract orientifold filter for the prime-gas/Fock corridor.

The fields are deliberately propositions so the module records the exact
topological hypotheses without introducing a fake proof of the Möbius law.
-/
@[rep_depth transport]
structure KleinBottleOrientifold where
  V4_Weyl : Prop
  V4_tensor_V4 : Prop
  V4_tensor_V4_tensor_V4 : Prop
  orientationReversingProjection : Prop
  kleinBottleQuotient : Prop
  fermionParity : Prop
  mobiusTwist : Prop
  squareAnnihilation : Prop
  squareFreeSupport : Prop

/--
Bridge packet tying the prime-gas MaxEnt data to the Klein bottle orientifold
hypotheses.

This is the topological filter surface: the prime gas remains a Jaynes packet,
and the orientifold effect remains an explicit hypothesis block.
-/
@[rep_depth transport]
structure OrientifoldPrimeGasPacket (D : PrimeGasJaynesData) where
  orientifold : KleinBottleOrientifold
  primeGas : InfoGeometry.Canonical.PrimeGasMaxEnt.PrimeGasJaynesData.PrimeGasJaynesConjecture D
  V4_projection : Prop
  fermionParity_projection : Prop
  moebiusSign : Prop
  support_kills_squares : Prop
  squareFreeSupport : Prop

/--
Topological support packet for the square-free sector.

This keeps the square-killing claim as a theorem-shaped surface rather than
as a kernel axiom.
-/
@[rep_depth transport]
structure SquareFreeSupportPacket where
  orientationReversingProjection : Prop
  fermionParity : Prop
  mobiusTwist : Prop
  squareAnnihilation : Prop
  squareFreeSupport : Prop

end InfoGeometry.Canonical.KleinBottleOrientifold
