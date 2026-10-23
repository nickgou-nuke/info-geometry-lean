# Attention routes: geometric and spectral scope

Intake: the conversation's proposed three-stage Transformer decomposition,
followed by the request to implement the highest-return gaps, not toy fixtures.
This record uses the epistemic-compilation workflow. Kernel evidence below
applies to the typed declarations, not to the stronger intake narrative.

## Priority and native owners

1. Connect deterministic vertices to the Drazin/Birkhoff boundary for arbitrary
   token counts. Reuse `DeterministicArgmaxAttention.deterministicAttention`,
   `Routing.AttentionPolytope.deterministic_mul`, Mathlib `doublyStochastic`, and
   `Canonical.Drazin.IsDrazinInverse`. Prove that a supplied Drazin witness has
   zero complementary projector exactly when the routing function is bijective,
   equivalently when its matrix is doubly stochastic.
2. Derive causal stabilization from the actual hypothesis `f i ≤ i`, and
   construct the Drazin inverse/core from a stabilized power. This is a uniform
   finite bound, not an assertion that the bound is the minimal index.
3. Consume the existing nonzero-causal-route theorem so the result applies to
   every nonzero route in a masked attention matrix's product-coupling expansion.
4. Eliminate route enumeration for expected causal core trace: prove it equals
   `trace(P)` for **any** exact causal coupling. Expose this as the exact-rational
   `expected_causal_core_rank` diagnostic and `--causal-core-only` CLI mode.

These are general operator results, not selected numeric examples. Existing
convex reconstruction and shell calculus are not duplicated. The causal and
permutation interfaces connect to them through the same matrix carrier.

## Corrected interpretation

- A square deterministic route is a functional graph. Row states advance along
  the route; column values are pulled back. Recurrent coordinate rows and the
  ambient column spectral core are not silently identified.
- An invertible deterministic vertex is a permutation vertex. A lower-dimensional
  recurrent permutation description requires explicit coordinates; the ambient
  Drazin inverse is not generally the transpose of its core.
- Dressed MP shells classify linear-state absorption, including cancellations.
  They are generally oblique, not diagonal token-depth selectors. Jordan/Lie
  sectors require the support commutation hypotheses recorded by their owner;
  no unproved nodewise leaf/relay/sink interpretation is attached.
- Carathéodory pruning preserves the specified output on fixed values. It need
  not preserve the attention matrix, spectrum, graph, or Drazin decomposition.
  Barycentric coordinates are unique only within a chosen affinely independent
  support. Rectangular routes do not acquire powers without a separate square
  construction.
- Route-mixture statistics require an explicit coupling. The existing
  `routeWeight` supplies the independent row coupling; alternative convex
  decompositions need not give equal general recurrent-core rank or depth.
  Causal core trace is an important proved exception: every recurrent point
  is fixed, and linearity makes its expectation `trace(P)` for every exact
  causal coupling. This is not the Drazin rank of the mixed matrix `P`.
  Neither statistic is established here as semantic reasoning depth.
- The Lean diagnostic proves core-projector **trace** equality; it does not
  separately formalize the rank–trace identification. The runtime name
  `expected_causal_core_rank` uses that mathematical interpretation, not an
  additional kernel-certified rank theorem. Runtime inputs require `n ≥ 1`;
  Lean's matrix results also allow the empty carrier.
- Linear-time graph traversal does not imply linear-time materialization of
  dense MP shell matrices. For rectangular attention, a removed-key fraction
  uses the key count, not the query count. A weight perturbation, rather than
  each removed key, lies in the homogeneous readout kernel.

## Preserved anomaly and graph context

The [Drazin/MP partition audit](DRAZIN_MP_PARTITION_AUDIT.md#anomalies-triple-products-and-graph-carriers)
records the existing Cantor triple-product, Jordan associator, chiral/Einstein
anomaly, and graph-differential owners. This routing bridge does not replace
those carriers or erase their noncommutativity. In particular, support-projector
commutators are not identified with the raw inverse commutator `[D,M]`, and
ordinary associative matrix multiplication is not a nonassociative product.
The new scalar trace diagnostic does not reconstruct those operator-valued
obstructions or assign their charges to individual tokens.

## Verification

The owner modules were checked with the repository locked Lake lane:

```text
InfoGeometry.Routing.CausalCoreTrace
InfoGeometry.Routing.CausalRouteDynamics
InfoGeometry.Routing.DeterministicDrazinBridge
InfoGeometry.Routing.CausalDrazinAudit
InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridge
InfoGeometry.Canonical.CantorBernoulliBoundaryRangeGNSBridgeAudit
```

The exact-rational attention tests pass (14 tests). The causal and GNS axiom
audits report only `[propext, Classical.choice, Quot.sound]`; semantic-vacuity
checks for the three routing owners report zero findings. No training-code
modification, interactive explorer, or full-model semantic classification is
claimed by this contract. The causal stabilization uses a sufficient `n`-step
bound; minimal Drazin-index and dense Moore–Penrose materialization remain
separate work.
