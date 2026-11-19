# Matrix Gibbs entropy: theorem contract and owner map

## Status and provenance

This draft closes the actual operator-logarithm connection between existing Gibbs,
normalization, entropy and free-energy owners. The source contains complete proof
bodies for **14 theorems and two definitions**. Independent mathematical/source
review passed on the exact source hash below. Native elaboration and the full
owned-declaration axiom audit remain required; this contract is not a kernel
acceptance certificate.

Source: `lean/InfoGeometry/Canonical/MatrixGibbsEntropy.lean`, SHA256
`a8f0a48d8f527f1cc1da85e8f53ef301ff0eda2404ec02f9e81a2acf158de359`.
Base: `08c34e03f610b452e03422037949196dc7d92d6d`.
Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Input: de Oliveira Junior, Brask, and Chaves, *A Friendly Guide to Exorcising
Maxwell's Demon*, PRX Quantum 6, 030201 (2025),
[DOI 10.1103/phkv-wrsd](https://doi.org/10.1103/phkv-wrsd).
The supplied PDF has 47 pages, 2,875,544 bytes and SHA256
`68b2415c86ddc54add9cabe0fa18cb0413020ee36d23ffc58e7b4026b7a43ea2`.
The independent [paper audit](MAXWELL_DEMON_INTAKE_AUDIT.md) records corrected
formulas, assumptions and counterexamples; it is broader than the Lean scope.

## Chosen contract

Owner: `InfoGeometry.Canonical.MatrixGibbsEntropy`.
Carrier: native `Matrix n n ℂ`, with `[Fintype n] [DecidableEq n]`.
Normalization additionally requires `[Nonempty n]`.
The Hamiltonian has `hH : H.IsHermitian`; `β : ℝ` is arbitrary unless a
free-energy division explicitly requires `β ≠ 0`.

The two definitions are derived from existing owners:

```text
W = FiniteMatrixGibbsFunctional.gibbsDensity H hH β
gibbsPartition H hH β = PolarFrameTraceDensity.traceMass W
normalizedGibbsDensity H hH β = PolarFrameTraceDensity.normalizedDensity W
```

Write `Z` for the partition, `Γ` for the normalized density, and `S` for the
existing `MatrixEntropyUnitaryOrbit.matrixEntropy`. The candidate derives:

1. `W = NormedSpace.exp ((-β) • H)` and `CFC.log W = (-β) • H`.
2. `Z > 0`, strict positivity of `Γ`, and `Matrix.trace Γ = 1`.
3. `Γ = Z⁻¹ • NormedSpace.exp ((-β) • H)`.
4. `CFC.log Γ = (-β) • H - Real.log Z • 1`.
5. For `Matrix.trace ρ = 1`,
   `Re Tr[ρ(log ρ - log Γ)] = -S(ρ) + β Re Tr(ρH) + log Z`.
6. `S(Γ) = β Re Tr(ΓH) + log Z`.
7. For `β ≠ 0`, the existing complex `QuantumRelativeSurprisal.freeEnergy`
   evaluated at the actual Gibbs state is `-log Z / β`; the actual
   relative-log trace is `β * (F(ρ) - F(Γ))`.
8. `β * (Re Tr(ρH) - Re Tr(ΓH)) = S(ρ) - S(Γ) + Re Tr[ρ(log ρ - log Γ)]`.

No commutation hypothesis on `ρ` and `H` occurs. Trace one suffices for the
algebraic comparison identities; positivity of `ρ` is needed for their
physical entropy interpretation, not for the trace algebra. The last identity
is same-Hamiltonian bath-energy accounting when `Γ` and `ρ` are the initial
and final bath states. It does not construct the joint physical evolution.

Actual dependencies are: native CFC composition and exp/log inversion →
existing trace normalization → actual normalized Gibbs logarithm → trace
identity → reference entropy/free energy and energy balance.

## Exact matrix owners reused

Paths below are relative to `lean/InfoGeometry/`.

| Owner | Actual declarations and assumptions | Boundary |
|---|---|---|
| `Canonical/FiniteMatrixGibbsFunctional.lean` | `gibbsDensity H hH β := hH.cfc (expWeight β)`; `gibbsDensity_strictlyPositive`; `gibbsPartition_ne_zero`; `gibbsFunctional`, `gibbsFunctional_one`, `gibbsFunctional_positive`, `gibbsFunctional_commutator_zero` | Arbitrary Hermitian complex matrix, arbitrary real inverse temperature. The existing KMS result is the algebraic boundary identity. No Gibbs-log theorem is present in this owner. |
| `Canonical/PolarFrameTraceDensity.lean` | `traceMass`, `normalizedDensity`, `traceMass_pos`, `normalizedDensity_isStrictlyPositive`, `trace_normalizedDensity`, `neg_log_normalizedDensity` | Full strictly positive matrices. The last theorem supplies exactly the central normalization correction specialized by the candidate. |
| `Canonical/MatrixEntropyUnitaryOrbit.lean` | `matrixEntropy_eq`; `log_unitary_conjugate`, `matrixEntropy_unitary_conjugate` require strict positivity; `matrixEntropy_normalizedDensity` | Genuine CFC density-weighted matrix entropy. No tensor additivity or subadditivity result was found here. |
| `Canonical/QuantumRelativeSurprisal.lean` | `relativeSurprisal`, `vonNeumannEntropy`, `freeEnergy`, `thermalModularHamiltonian`; `relativeSurprisal_eq_beta_freeEnergy_diff` requires complex inverse temperature nonzero and trace-one source | Existing algebra takes supplied log matrices. The candidate proves the actual Gibbs-log identification and then instantiates this theorem. |
| `Canonical/NoncommutativeGibbsFaithfulNormalizationBridge.lean` | `exp_isStrictlyPositive`, `faithfulGibbsDensity`, `faithfulGibbsDensity_rho_eq_normalizedExponential`, `faithfulGibbsDensity_rpow` | Actual finite operator carrier; positive partition readout is an explicit `hZ` premise. No logarithm theorem in this owner. It is not needed as an import for the chosen matrix leaf. |
| `OperatorAlgebra/NoncommutativeRenyi.lean` | `stateSurprisal`, `relativeLogDensity`, `umegakiKernel`, `umegakiRelativeEntropy` | Actual CFC kernels and positive-functional readouts. The candidate trace expression is this Umegaki kernel on matrices; no duplicate kernel or relative-entropy carrier is defined. No general Umegaki nonnegativity theorem was found in this owner. |

Candidate imports are only `FiniteMatrixGibbsFunctional` and
`MatrixEntropyUnitaryOrbit`. Root's source-only closure calculation reports
seven existing repository owners and 23 native Mathlib roots: the four core
matrix owners above plus `FiniteSpinAlgebra`, `MatrixDetExpTraceJacobi`, and
`FiniteBogoliubovFrameDeformationEntropy`.

Exact pinned native declarations inspected: `Matrix.IsHermitian.cfc_eq`,
`cfc_comp_smul`, `CFC.real_exp_eq_normedSpace_exp`, `CFC.log_exp`,
`CFC.log_smul'`, `RCLike.real_smul_eq_coe_smul`, and matrix trace linearity.
CFC composition conversion and real/complex scalar transport remain ordinary
elaboration risks until the serialized native check runs.

## Finite-law and reset owners

| Owner | Actual result | Small missing implication or limit |
|---|---|---|
| `Probability/FiniteGibbsVariational.lean` | `finiteRelativeEntropy_gibbs_eq`, `finite_gibbs_variational_identity`, `gibbsFreeEnergy_le` on actual normalized finite real vectors | Nonnegativity/minimization contracts require strict positivity; minimization needs `β > 0`. Do not duplicate this scalar Gibbs identity. |
| `MaxEnt/IProjection.lean` | `toReal_klDiv_eq_sum_log_ratio`, `sum_log_ratio_nonneg` for arbitrary finite source PMF against a full-support reference PMF | Useful native KL bridge allowing zero source weights. |
| `EntropicInference.lean` | Actual PMF marginals, support-indexed conditionals, assembly; `kl_chain_rule_toReal_strict`; `kl_marginal_x_eq_toReal_iff_conditionals_eq`; `kl_marginal_x_eq_toReal_iff_exists_shared_recovery` | Both joint laws are strictly positive in these KL-chain/equality results. A deterministic graph joint has zeros. |
| `Canonical/FiniteBipartiteSurprisal.lean` and `Canonical/IBBase.lean` | The former defines `entropyMutualInformation` by the entropy difference on actual PMFs; the latter defines `mutualInformation` by native finite KL | The identity connecting these two existing definitions was not found in the inspected sources. A later implementation should bridge them instead of creating a third definition. |
| `Canonical/DeterministicArgmaxAttention.lean` | `conditionalEntropy_zero`, `mutualInformation_eq_entropyKey`, `mutualInformation_bijective_eq_log_N` | Correct deterministic forward conditional-entropy direction already proved for uniform finite input. General PMF pushforward and support-injective loss characterization remain useful extensions. |
| `Canonical/HierarchicalGibbsEntropy.lean` | `jointEntropy_eq_sectorEntropy_add_expectedConditionalEntropy` | Actual entropy chain for a strictly positive hierarchical Gibbs family, not a general support-aware PMF chain. |
| `Canonical/CoarseGraining.lean` | Actual finite maps, `fiberWeight`, `totalWeight_eq_sum_fiberWeight` | Reusable pushforward summation; no generic Shannon loss theorem. |
| `Quantum/FinitePartialTrace.lean` | Actual matrix partial trace, trace preservation and diagonal marginal formula | Namespace is `InfoGeometry.Quantum.FiniteAttentionCanonicalBridges`; no marginal entropy theorem. |
| `Quantum/ReplacementStateChannel.lean` | `replacement σ X = trace X • σ`; trace preservation for trace-one `σ`; `replacement_on_density`; complete positivity for all finite ancillas when `σ` is PSD | A genuine reset channel exists. This alone does not construct a reservoir dilation or its entropy/heat cost. |

`LandauerDissipationNativeBridge` defines a scalar heat formula and proves its
positivity; `LandauerCramerRaoBoundBridge` defines `kBT log 2 * ΔS` and proves
scalar consequences. These do not establish microscopic entropy balance.
`Thermal.VonNeumannEntropy` is a two-level scalar formula.
`Modular.QuantumDataProcessingInequality` uses positive spectral probability
vectors and classical KL, not arbitrary noncommuting Umegaki relative entropy.

Alternate Omega sources were read as well. `SideinfoExactEntropy` has
arithmetic/cardinality seeds; `MinDisambiguationTimeEntropyDecomposition`
assumes the KL/entropy equality; `ChebotarevQuotientRelativeEntropyChain`
stores that equality in a structure; `LayeredExternalizationAverageShannonBudget`
assumes layerwise coding bounds. `XiTimePart62EAChiLYExactInformationLoss`
proves one explicit uniform three-state `1:2` split. These inspected sources
do not supply a general PMF conditional-entropy theorem.

## Consumers inspected

`MatrixEntropyUnitaryOrbit` has no direct non-aggregator importer in the
inspected main tree. `QuantumRelativeSurprisal` is imported by it.
`PolarFrameTraceDensity` also feeds `PolarFrameBKMGeometry`,
`OperatorLogDetDikinGeometry`, and `OperatorAlgebra.TracialGNSMatrixTests`.
`FiniteMatrixGibbsFunctional` feeds faithfulness, centralizer, operator-readout,
compatible-state-net, matrix-purification and stage-product-density owners.
The isolated leaf requires no existing-owner edit.

`EntropicInference` feeds finite-channel data processing, `IBFinitePythagorean`,
and `FiniteBipartiteSurprisal`. Deterministic attention feeds
`Routing.AttentionPolytope`. Replacement channels feed
`PeirceHistoryRecoveryError` and `ZornHistoryQuantitativeRecovery`.
These are source dependencies, not downstream compilation results.

## Open-PR overlap checkpoints

The following records are observed GitHub metadata/source. No reported CI
result was independently re-executed for this receipt.

| PR | Exact observed head/status | Overlap decision |
|---|---|---|
| [358](https://github.com/nickgou-nuke/info-geometry-lean/pull/358), reconstruction/Landauer erasure | `473d39724c43ee5cef8ba971ff82dfe42ca084f4`; open, draft, unmerged | Actual `BinaryErasure`, `Jarzynski`, `TraceErasure`, `ObservableErasure` fetched. Imperfect binary reset, finite exponential-moment/Jarzynski inequalities and algebraic reset/fixed-observable results are already proposed. Work bounds consume fluctuation/moment or entropy-balance premises. The inspected owners do not derive the actual complex matrix Gibbs logarithm or joint thermal entropy balance. |
| [370](https://github.com/nickgou-nuke/info-geometry-lean/pull/370), Hodge/Kraus fixed effects | `a56bf9e6655c1086d7654b6c4d1eeab705484a5c`; open, draft, unmerged | Exact `KrausUniversalFixedEffects` constructs reset Kraus families, proves completeness and trace-reset readout, and characterizes universal fixed effects as scalars. No entropy/heat balance in this owner. |
| [392](https://github.com/nickgou-nuke/info-geometry-lean/pull/392), real BKM constraints | `5ddf3e6b50c291d1340eee922e15ae8415d8652a`; open, draft, unmerged; native acceptance pending in current description | Exact `RealBKMGibbsStationarity` proves exp of negative supplied spectral surprisal, then normalization from an assumed affine-surprisal equation. It does not prove arbitrary Hermitian complex CFC Gibbs-log or relative-log/free-energy identities. Distinct scope. |
| [385](https://github.com/nickgou-nuke/info-geometry-lean/pull/385), currents/associator dissipation | `e1bbd7950c8d7938beaa8193efdc88937bc15391`; open, draft, unmerged; latest repaired-head acceptance pending in description | Exact changed-file list contains currents, split-octonion/projected dissipation, a causal-owner import repair, docs and workflow. Gibbs/Landauer search hits are boundary prose. No Gibbs entropy owner is changed. |

Bounded queries covered Maxwell, Szilard, Landauer, entropy, conditional
entropy, information loss, reset, Gibbs/log, and free energy. This is a
bounded source-backed absence result, not a claim of exhaustive global recall.

## Remaining mathematical work

Full quantum Landauer requires actual joint dynamics, tensor-product entropy,
marginal entropy identities/inequalities, nonnegative quantum relative
entropy or mutual information, and support treatment. Existing unitary
matrix entropy invariance, partial trace and CP reset do not alone close it.

A later finite classical theorem could start from an actual PMF on `A × B`,
an initial product with a Gibbs bath, and a permutation/equivalence of the
joint state space. Derive entropy conservation and product additivity, then
`βQ = H(initial system) - H(final system) + MI(final joint) + KL(final bath || Gibbs)`.
This needs a support-aware Shannon chain and its native KL bridge first.

The independent paper audit separately records printed sign and conditional-
entropy errors. Deterministic `Y=f(X)` gives `H(Y|X)=0` and `I(X;Y)=H(Y)`;
the reverse conditional vanishes only when the observation is injective on
the source support. No erroneous paper sign is incorporated into this
candidate.

## Verification design and source review

The independent Lean review returned `PASS_SOURCE_REVIEW_KERNEL_UNVERIFIED`
with no required changes. It checked all 16 source declarations, native CFC
composition/log-exp inversion, real/complex scalar transport, trace linearity,
noncommutative order and explicit hypotheses against the pinned sources.
The original source-review receipt SHA256 is
`c7dffb7232f6561825cd5a430510d838627e249a31d70efa75983ec5eb32682e`.
This receipt records source inspection, not execution acceptance.

The focused workflow `.github/workflows/matrix-gibbs-entropy.yml` checks the
exact PR head. It resolves and freshly compiles the complete repository source
closure, audits every declaration owned by the selected module, requires zero
selected-owner compiler warnings and permits only `propext`, `Classical.choice`
and `Quot.sound`. It restores no repository proof artifacts and uses neither
incremental proof reuse nor an audit skip. Runtime and Mathlib pins are checked;
the Lean archive checksum is verified on every run before extraction. Reports,
logs, source snapshots and source/workflow provenance are retained per attempt.

The expected closure has eight repository modules and 23 existing Mathlib import
roots. The workflow records and reconciles the actual dynamically resolved
closure instead of trusting those expected counts. Scoped acceptance does not
establish an `InfoGeometry.All`, root Lake, consumer or pre-push pass. The
repository's actual hooks and static source gates remain separate checks; their
current results and native run links belong in the PR's validation record.

Native checks and first-run elaboration errors, if any, must be resolved before
this draft is treated as kernel accepted. No full quantum Landauer inequality,
relative-entropy minimum, joint dynamics or physical implementation is claimed.
