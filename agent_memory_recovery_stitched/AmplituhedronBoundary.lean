import Mathlib.Tactic
import InfoGeometry.Projective.ArnoldRelations

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
