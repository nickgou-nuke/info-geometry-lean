# Pre-code source discovery: graph Hodge, projective affinities, Kramers and Zorn pairing

Source target: `Pasted text(20260905-170709).txt` (not the previous attention attachment).
Search completed before the new Lean modules were written.

The default-branch code search returned commit
`b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`.
The projective/gauge dependency snapshot is the existing branch
`projective-zorn-attention-state-geometry` at
`71e683c8388acfd6101d554aaec0771cc886d2a2`.
The PR description at #150 has since been replaced with an unrelated Freudenthal
narrative while the branch and commit remain the same. It is not used as source
truth. The actual source files and their exact commit are the dependency evidence.
No mutation of that PR or of either existing branch is requested by this work.

## Search passes

Default-branch queries: `DiracHodge`, `Schnakenberg`, `Kramers`,
`SchnakenbergDecomposition`, `Andreev`, `BdG square`, `hodgeDecomposition`,
`orthogonalProjection`, `stochasticEntropyProduction_nonneg`.
Pull-request search: `Dirac Hodge`, including open and closed PRs.
Proof ownership was decided by fetching executable `.lean` source, not by
archived notes, generated audit warnings, names, or PR descriptions.

## Reused rather than reimplemented

| Source owner | Actual content inspected | Decision |
| --- | --- | --- |
| `Topology/DiscreteDiracHodge.lean` | Concrete three-degree cochain maps, degree chirality, nilpotence inputs, `D^2` identity | Do not introduce the attachment's duplicate `Omega`, `d`, `delta`, `D` |
| `Topology/EckmannDiscreteHodge.lean` | Transpose-adjoint dot identity, positivity, Laplacian kernel/closed+coclosed theorem | Reuse its mathematical boundary; no claimed missing basic Hodge square |
| `Topology/HodgeDecomposition.lean` | Native exact/coexact/harmonic submodules; decomposition proposition, not its universal construction | Does not yet construct the particular graph cycle/cocycle decomposition |
| `Canonical/ThermodynamicChiralGraphCalculus.lean` | Actual graph fields, outgoing-minus-incoming incidence, rate and flux affinities, positive-flux entropy kernel, `SchnakenbergDecomposition` | Construct this existing decomposition record; do not create another graph or thermodynamics record |
| `Canonical/SupergradedGraphEntropyHodgeBridge.lean` | Composition of existing owners; supplied Hodge closure packet and entropy-positivity wrappers | Not a constructor of the graph decomposition |
| `Canonical/HestenesKramersBridge.lean` | Actual internal phase partner, square minus identity, Hilbert orthogonality, Krein anti-isometry | Do not rebuild orthogonality or conflate Hilbert and Krein metrics |
| `Canonical/HestenesRealStructures.lean` and `TimeReversalKramers.lean` | Distinct intrinsic phase axis and phase-antilinear Krein-isometric symmetry data | Extend no-real-eigenvector consequence while preserving the distinction |
| `Physics/BdGChiralBlockMatrix.lean` | Native associative coefficient-block identities, explicit disclaimer that this is not a Zorn algebra | Do not replace the Zorn field carrier with this matrix algebra |
| `Canonical/DiscreteDiracKahlerLaplacian.lean` and `DiscreteHodgeStarAndCoderivative.lean` | Split-octonion calculus with separately supplied nilpotence/left-reassociation hypotheses | Do not transfer alternativity to noncommuting operator coefficients |
| `Canonical/OperatorZornFourPotentialGauge.lean` at projective parent | Actual coefficient derivation and Leibniz proof, native Zorn associator, arbitrary direction labels | Reuse in the full bilayer action; retain all corrections |
| `Canonical/OperatorZornRealModule.lean` at projective parent | Additive real module on the same NC-Zorn carrier, scalar bilinearity only | Use native LinearMap structure without a Ring instance on Zorn |
| `Projective/ExpectationRatioMetric.lean` at projective parent | Existing positive-ray quotient and normalized expectation | Use the existing ray/scale spine, not external spacetime |

## Unmerged graph implementation found

PR #148, branch `causal-boundary-gauge-g2-reconstruction`, exact commit
`b1dfa58b95c25b3f5cf913e571013dd02e681e38`, already has
`Streaming/BipartiteGraphDirac.lean`. Its source was fetched, not just its PR body.
It constructs the actual rectangular-incidence graph differential and transpose
codifferential, proves their nilpotence/adjoint relation, and reuses the existing
Dirac--Hodge theorem. It also proves grading anticommutation and graph energy.
This work does not duplicate that module or silently import an unmerged file
not present in the chosen parent. Its publication/verification status remains
separate from the new work.

## Chosen next obligations

1. Prove finite graph integration by parts with the owner's incidence sign;
   construct its existing Schnakenberg decomposition from native orthogonal
   projection, including uniqueness rather than accepting it as data.
2. Put the owner's stochastic probability/current/affinity readouts on the
   existing positive-ray quotient. Use actual positive fluxes for entropy,
   retaining reference ratios and proving steady cycle-only production.
3. Extend the already implemented real phase partner to absence of all real
   eigenvectors, not merely absence of fixed vectors. Do not call a real
   square-minus-one structure alone an antiunitary Kramers theorem.
4. Construct the bilayer as a linear action on two copies of the unchanged
   operator-Zorn module. Its square keeps both the derivative of the gap and
   the associators. A nonzero Zorn coupling is not assumed to be a positive
   spectral lower bound.

## Verification boundary

Fetched source scripts are implementation evidence, not proof of a successful
native build in this environment. The parent snapshots are unverified here.
No missing theorem is inferred from a keyword search alone; the explicit
construction target is the existing Schnakenberg record and its actual fields.
