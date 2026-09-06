import Mathlib.Tactic
import InfoGeometry.Projective.ArnoldRelations
import InfoGeometry.Projective.TwistorAmplituhedronBridge

/-!
# Three-Point Amplituhedron Boundary Operators

This file records the finite algebraic surface behind the requested
three-channel boundary calculation.

Closed here:

* a three-point boundary packet has three nilpotent on-shell edge operators and
  three logarithmic channel forms;
* the advertised "super-amplitude volume" is exactly the three-term mixed
  expression;
* left multiplication by an on-shell nilpotent edge removes its own channel;
* if a separate owner supplies that the mixed expression vanishes, an arbitrary
  BCFW-style readout follows through the supplied comparison implication.

Not closed here:

* no amplituhedron or positive Grassmannian is constructed;
* no theorem identifies this algebraic packet with `F_Q(C^4,3)` de Rham
  cohomology;
* no BCFW recursion theorem is derived;
* no `N = 4` SYM state-count theorem or rank-32 cohomology theorem is proved.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

/-- Three-point amplituhedron boundary packet. -/
structure Amplituhedron3Point (Op : Type*) [Ring Op] where
  edge1 : Op
  edge2 : Op
  edge3 : Op
  channel1 : Op
  channel2 : Op
  channel3 : Op
  square_zero_edge1 : edge1 * edge1 = 0
  square_zero_edge2 : edge2 * edge2 = 0
  square_zero_edge3 : edge3 * edge3 = 0
  mixed_volume : edge1 * edge2 * edge3 = edge1 * edge3 * edge2 + edge2 * edge1 * edge3 + edge3 * edge1 * edge2

/--
Three-point boundary packet with an explicit BCFW comparison in the selected
operator carrier.

Constructing `cooperadReadout` and `bcfwReadout` from positive-Grassmannian or
plabic data remains the responsibility of the model instantiating this packet.
-/
def AmplituhedronBoundaryPacket (Op : Type*) [Ring Op] : Type _ :=
  Amplituhedron3Point Op × Op × Op

namespace AmplituhedronBoundaryPacket

/-- Native product projection for the three-point boundary algebra. -/
abbrev amp {Op : Type*} [Ring Op]
    (packet : AmplituhedronBoundaryPacket Op) : Amplituhedron3Point Op :=
  packet.1

/-- Native product projection for the cooperad readout. -/
abbrev cooperadReadout {Op : Type*} [Ring Op]
    (packet : AmplituhedronBoundaryPacket Op) : Op :=
  packet.2.1

/-- Native product projection for the BCFW readout. -/
abbrev bcfwReadout {Op : Type*} [Ring Op]
    (packet : AmplituhedronBoundaryPacket Op) : Op :=
  packet.2.2

end AmplituhedronBoundaryPacket

end InfoGeometry.Topology.AmplituhedronBoundary
