# Binary reciprocal-odds gluing

## Search and reuse

Searched filenames and declaration bodies across `lean` and `proofs`, the
local declaration index, and external references. Also ran context preflight
for `mappingTorus endpointStep involution barrier quotient`.

Inspected these existing owners before finalizing the implementation:

- `Topology/MappingTorusGluing`: endpoint rule and equivalence closure on
  the entire real line times a fibre. Reused its `endpointStep` rule with
  an explicitly restricted base carrier.
- `Topology/SplitOctonionMirrorRailMappingTorus`: specialization of that
  same real-line quotient, not the interval restriction needed here.
- `Topology/MirrorAnomalyPairing`: conditional cancellation for a supplied
  odd observable, not descent of a symmetric barrier.
- `Topology/KleinAffineOrbitQuotient`: a different affine deck-group orbit
  quotient; not the binary interval mapping torus.
- `Analysis/BipolarCrossRatioLog`: reciprocal complex odds under endpoint
  exchange. `Convex/BipolarLogitBarrierDuality` already supplies the real
  logit antisymmetry and symmetric interval barrier used here.
- `LanglandsGWBridge`: a chirality-flip involution, not this topological
  quotient. No matching barrier-descent theorem was found in the index.

## Construction

`Topology/BinaryBarrierTwistedGluing.lean` uses
`Cylinder = [0,1] × (0,1)` and identifies `(0,p)` with `(1,1-p)`.
The flip is bundled as a homeomorphism and is involutive. Odds transform
by reciprocal inversion and the logit changes sign.

The native quotient topology is installed. The symmetric barrier
`-log p-log(1-p)` respects every step of the generated equivalence relation,
so `Quotient.lift` defines a unique descended function. Continuity is proved
from the existing derivative theorem and the quotient topology.

The probability fibre is open because the finite real-valued barrier is
defined there. This is not a proof of compact Möbius-band classification,
nonorientability, or a physical/modular-time interpretation. Those remain
separate statements. Existing real-line quotient users are unchanged.

Validation targets: `InfoGeometry.Topology.BinaryBarrierTwistedGluing` and
`InfoGeometry.Topology.BinaryBarrierTwistedGluingAudit`, through the shared
locked-build runner. This is scoped verification, not repository-wide release.
