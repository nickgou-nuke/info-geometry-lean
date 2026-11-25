# Neutral graph mirror, spinor minors, and finite bipartite contractions

## Provenance and environment

Intake: the user's 2026-11-25 `PlabicDiracCourantUnification.lean` proposal
and its three-part mathematical narrative. The proposal asserts a positive
epsilon cross-pairing and claims compilation; that sign is false for its
displayed epsilon matrix. The input is a candidate, not a verification receipt.

Base repository: `nickgou-nuke/info-geometry-lean`, revision
`fe24e350b08fdea04f74c0748ef9fd9417c47529`. Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged.

The predecessor's unpublished `SkewGraphNeutralPairing` and `MatrixDiracGraphs`
owners are reused in this independent checkout. `SkewGraphNeutralPairing`
has proof-script repairs for simplification through linear maps and local
identifier spelling; its declarations and hypotheses are unchanged.
`MatrixDiracGraphs` remains identical to the predecessor source at the latest
review. The reviewed source hashes and repair details are in REVIEW.md.
Their full import closure must be compiled here; prior staging is not proof.

## Exact contract

1. On the native real dual phase space `E × Module.Dual ℝ E`, define the
   primal-sign mirror as the negative of the existing `neutralParaInvolution`.
   Prove involution, anti-isometry, transport of actual graph submodules, and
   the fixed graph locus as the kernel image. No skew hypothesis is needed.
2. Reuse matrix graph isotropy, maximality, and the cross factor two. Normalize
   the cross-pairing by one half. With epsilon `[0,1;-1,0]`, prove that the
   result is minus the determinant bracket. Prove the explicit sign
   counterexample and trivial kernel of epsilon.
3. Transport the existing `Amplituhedron.plucker_relation_general` through
   these minors. The two minus signs cancel in each quadratic product.
4. Prove closure of skew matrices under addition and rectangular congruence,
   graph forward image under `Q`, and shared-kernel inclusion. Do not confuse
   the graph of a sum with the subspace sum of graphs.
5. Connect edge contractions to the existing finite bipartite/Kasteleyn owner.
   The epsilon edge weight is minus twice the determinant bracket, so the
   signed edge matrix and real block Dirac operator scale by minus two.
6. Record the mirror parity law for products of scalar edge contractions.

## Owners and dependency order

- `Clifford.NeutralPhaseSpaceCore`: actual dual carrier, neutral form,
  `neutralParaInvolution`, its square and anti-isometry.
- `Geometry.SkewGraphNeutralPairing`: actual graph submodule, maximal
  isotropy, opposite-graph intersection and complement criteria.
- `Geometry.MatrixDiracGraphs`: native `dotProductEquiv` coordinate transport.
- `Topology.AmplituhedronGeneralTwistorExpansion`: real specialization of
  the commutative-ring minor and Plücker identity.
- `Canonical.FinitePlabicKasteleyn`: finite endpoint/edge/face data, supplied
  signing, signed edge matrix, and block Dirac operator.

The proof order is evaluation pairing -> graph geometry -> mirror/kernel and
matrix transport -> real two-dimensional minors -> Plücker and edge weights.

## Interpretation boundaries

The statements concern linear algebra and finite combinatorial data.
An integrable Courant subbundle, a Lie bialgebra/Drinfeld double, a physical
CPT action, a planar embedding, boundary measurement, and spin-network
intertwiners are not constructed. Kernel covectors become Casimir functions
only with an explicit differential condition; no entropy identification is
asserted. General plabic graphs need not be bipartite. Nondegenerate epsilon
has no nonzero mirror-fixed graph states. A mirrored scalar edge product
has sign `(-1)^card`, so invariant amplitudes need additional structure.

The Plücker identity holds for arbitrary spinor families, including those
whose two-row matrix has rank below two and whose minors all vanish. A
nonzero Plücker coordinate vector, equivalently rank two in this matrix
setting, is an additional requirement for representing a point of
`Gr(2,n)`. Neither that requirement nor positivity of minors, edge weights,
or boundary measurements is derived here. The finite graph and its
Kasteleyn signing are supplied data; their geometric realization and the
existence of such a signing are not constructed by these bridge theorems.

## Acceptance and reporting

Compile the exact dependency closure at the pinned environment, with warnings
as errors for added owners; inspect every added module-owned declaration's
axioms, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Run the
maintained narrow root wrappers and staged proof gate. Record isolated-source
verification separately from root-package resolution, and preserve all caches.
An independent source review must inspect the final declarations and scope.

## Primary references

- Bursztyn, *A Brief Introduction to Dirac Manifolds*, Sections 3 and 5:
  https://w3.impa.br/~henrique/papers/villadeleyva.pdf
- Postnikov, *Total Positivity, Grassmannians, and Networks*, Sections 11–12:
  https://math.mit.edu/~apost/papers/tpgrass.pdf
