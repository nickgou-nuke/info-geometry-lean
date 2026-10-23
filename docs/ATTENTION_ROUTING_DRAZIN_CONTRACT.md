# Attention routes: geometric and spectral scope

## Intake audit: proposed eight-module / PyTorch master table

Source: the follow-up conversation headed “Master Summary Table: Lean 4
Theorems ↔ Mathematical Statements ↔ PyTorch Implementation”, audited against
checkout `62d48fc0b8296fdbd9528d13c1f5495bc81e3a31` on 2026-10-23.
Disposition: **needs correction; not a publication-ready verification table**.
This section supersedes the intake's verification/count and runtime claims,
not the independently recorded scoped checks below.

The intake enumerates **nine** distinct proposed added module names, not eight
(plus its proposed baseline). Neither “38 theorem blocks” nor the claimed
eight-file compilation follows from the supplied prose. Exact filename scans,
including hidden/untracked paths but excluding dependency/build/runtime caches,
did not locate `AttentionLearningAudit.lean`, `train_entropic.py`, or
`polytope_drazin_diagnostics.py`. The named audit-suite files and implementation
symbols were not found in the searched repo-owned source surfaces. This is a
checkout-scoped finding, not a claim about files in another workspace.

Recounted intake labels: `BirkhoffPolytopeAudit`, `AttentionSimplexAudit`,
`AnalogyAffineAudit`, `ProjectiveCaratheodoryAudit`, `CaratheodoryPruningAudit`,
`DrazinMoorePenrosePartitionAudit`, `NilpotentShellFiltrationAudit`,
`DrazinNilpotentShellResolutionAudit`, and `DrazinShellDynamicsAudit`.
The exact-symbol source scan included `caratheodory_compression_theorem`,
`caratheodory_pruning_step`, `barycentric_injective_iff_affineIndependent`,
`normal_drazin_eq_moorePenrose`, `permLaplacian_isNormal`,
`operator_core_isomorphism_and_shell_cascade`, `analogy_affine_extrapolation`,
`build_exact_drazin_shell_matrices`, `PolytopeDrazinAttentionDiagnostics`, and
`BirkhoffPolytopeAttentionBlock`, across `lean tools scripts src proofs tests`.

### Source-backed replacement map

| Intake claim | Inspected native owner / declaration | Honest scope |
| --- | --- | --- |
| Deterministic routes and convex readout | `Routing.AttentionPolytope`: `convexHull_deterministic_eq`, `matrix_readout_decomposition`, `token_readout_mem_convexHull` | Exact rectangular stochastic readout; not compression or inverse transport |
| Birkhoff/Drazin boundary | `Routing.DeterministicDrazinBridge`: `deterministic_doublyStochastic_iff_complement_zero` | Deterministic square vertices only; not arbitrary mixtures or their Laplacians |
| Causal route core | `Routing.CausalRouteDynamics`: `causal_deterministic_drazin`, `causal_deterministic_core` | Sufficient stabilization bound; not minimal-index computation |
| Expected causal core statistic | `Routing.CausalCoreTrace`: `causal_mixture_core_trace` | Core-projector trace equals `trace(P)` for any exact causal coupling |
| EP inverse agreement | `Canonical.NormalSemisimpleAgreement`: `drazinInverse_eq_moorePenrose_of_isEP` | Explicit MP, Drazin and EP hypotheses; the filename does not supply a normality-to-EP proof |
| Regularized Markov inverse | `QuantumContext.MarkovAttentionGroupInverse`: `kemeny_snell_fundamental_invertible` | Two-sided inverse with the complete kernel projector retained |
| Raw and dressed shells | `Canonical.DrazinNilpotentShellResolution`: `drazin_core_and_nilpotent_shells_partition_of_unity`, `drazinShellProj_not_absorbed_at_m` | Generic star-ring algebra; exact right-action absorption, oblique dressed idempotents |
| Anomaly-sensitive sectors | `Canonical.InverseKernelSectorAnomalies`: `spectral_metric_sector_sum`, `spectral_range_sector_sum`, `spectral_metric_jordan_associator` | Retains noncommuting projector defects and the Einstein sign convention |
| Executable route readout and causal trace | `tools/attention_polytope.py`: `decompose`, `route_readout`, `expected_causal_core_rank` | Exact rational Python; not PyTorch, training integration, or certified floating-point execution |

Source inspection is not a new kernel check of every row. See the verification
record for the explicitly executed targets. No invented audit names are added
as aliases to make the intake table appear implemented.

### Mathematical corrections required before publication

1. **The regularized inverse is not the pseudoinverse.** With
   `L = I − Πσ` and the full orthogonal kernel projector `Π₀`, the normal
   finite-dimensional endpoint satisfies
   `(L + Π₀)⁻¹ = L† + Π₀`, hence
   `(L + Π₀)⁻¹ (I − Π₀) = L†`.
   A permutation can have several cycles, so `Π₀` need not have rank one.
   An endpoint identity proves no temperature-limit convergence: rank can
   change, and pseudoinversion is not generally continuous across rank changes.
   Normality implies minimal Drazin index at most one; a witness predicate
   supplied with exponent `k` does not imply that this particular `k ≤ 1`.
2. **Analogy coordinates need independence.** The parallelogram equation gives
   one affine expression with coefficients `(-1,1,1)`. Uniqueness requires the
   three selected values to be affinely independent. Only under that condition
   does this expression exclude the target from that triple's convex hull.
   It does not exclude the target from a larger value dictionary, nor prove
   a general architectural necessity for residual/multihead subtraction.
   A uniform matrix-level identifiability iff also needs a nonempty query
   carrier; with zero queries the implication is vacuous.
3. **Compression is readout-specific, not universal KV eviction.**
   Carathéodory gives a sparse representation for a fixed output, with a
   potentially different support for each query. The union of those supports
   can include every key. It does not preserve logits, future-query outputs,
   attention spectra, or training gradients. A constructive pivot algorithm,
   mask/support preservation, termination, and floating-point error contract
   are additional implementation obligations. Mathlib's
   `Analysis.Convex.Caratheodory` owns the convexity theorem; no native
   attention pruning algorithm was identified in this search.
4. **Shells are not node-depth bins.** Range shells concern covectors under
   right action; co-range shells concern columns. Dressed shells are algebraic
   mutually annihilating idempotents, not necessarily orthogonal projections
   in the metric sense. Their ranks/entries cannot be replaced by hop-depth
   counts or leaf/relay/sink fractions without a separate theorem. The
   right-action absorption and core-power recovery declarations inspected here
   do not alone certify the claimed faithful leading-step cascade theorem.
5. **Jordan/Lie hypotheses cannot disappear from the LaTeX table.** Write
   `p = XM`, `q = MX`, so `[X,M] = p − q`. The three-sector expression with
   squared support difference `(p − q)²` satisfies
   `pq + (p − q)² + (1 − p)(1 − q) = 1 + [p,q]`.
   Its interpretation as a three-projector partition requires commuting MP
   supports; `[p,q]` is distinct from `[X,M]`. Zero trace
   of a commutator is not by itself a discrete Stokes theorem. The bracket
   with an MP inverse is self-adjoint, not a skew-adjoint matrix merely because
   the bracket is antisymmetric in its arguments.
6. **Scaling is algebraic, not attention-polytope invariance.** Nonzero scalar
   rescaling preserves inverse-support products, but `cP` usually ceases to be
   row-stochastic when `c ≠ 1`. This is not a proved local Weyl symmetry or
   invariance of a full attention/training pipeline.

### Highest-return outstanding integrations from this intake

Prioritize general native consumers, not additional small matrix witnesses:

1. A support-preserving attention compression theorem returning actual key
   indices/weights and a matching executable pruning/error contract, reusing
   Mathlib Carathéodory rather than duplicating its geometry.
2. Complete integration and acceptance of the claimed strict shell cascade and
   faithful leading-step interface on the existing generic dressed-shell
   carrier, followed by an explicit comparison with functional-graph depth
   (not an assumed equality). Concurrent `Canonical/DrazinShellCascade` work
   was reported during QA and is excluded from this audit's acceptance;
   this item is not a repository-wide absence claim.
3. A real tensor-runtime integration contract once the claimed training source
   is supplied: shapes, masks, normalization, centering, tolerance, and gradient
   behavior. The present exact-rational tool does not discharge this obligation.

The previously recorded Cantor/associator/chiral/Einstein owners remain part of
Track B's context. Scalar statistics and graph visualizations cannot substitute
for their operator-valued statements.

Fresh bounded check for this intake: the locked build of
`InfoGeometry.Routing.CausalDrazinAudit` and
`InfoGeometry.Canonical.DrazinNilpotentShellAudit` completed successfully
(8943 jobs). The audit output reports only standard foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) or no axioms. Existing dependency
warnings remain. This does not verify the proposed pruning modules, alleged
training code, temperature limits, or the entire manuscript table.

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

### Independent routing acceptance (2026-10-23)

`[accepted_limited_scope]`: A-A Darwin passed the three routing owners,
runtime diagnostic, and corrected documentation. Independent QA-A Singer ran
the locked `InfoGeometry.Routing.CausalDrazinAudit` build (8939 jobs), four
sequential direct Lean checks under the shared lock, and all 14 Python tests.
All passed. The eight audit declarations use only `propext`,
`Classical.choice`, and `Quot.sound`; semantic-vacuity, placeholder/unsafe,
header, and scoped whitespace checks passed. Code/test hashes stayed stable
throughout QA. Direct checks reported no local Lean warnings; replayed
dependency warnings and existing dependency-local changes remain.

This acceptance covers the three routing owners, their axiom audit, and the
runtime diagnostic/tests. It does not accept concurrent Cantor/GNS or
`DrazinShellCascade` edits, the entire shared index, or the full repository.
