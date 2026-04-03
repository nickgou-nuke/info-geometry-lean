# One Theory, Many Presentations

This repository is best read as a stratified tower of presentations of one underlying theory.
The important mathematical content is not only in the objects at each layer, but in the coherence theorems proving that different adjacent translation paths agree.
Those adjacent morphisms are the main formal target.
The repository should not be flattened into one facade surface; it should make the representation changes explicit and check that they commute.

The representation grammar is now partially enforced natively inside Lean:
- [Architecture.lean](lean/InfoGeometry/Meta/Architecture.lean) defines depth metadata and the dependency-span audit
- [Audit.lean](lean/InfoGeometry/Audit.lean) is the CI entrypoint

Python reports remain useful, but they are downstream views over a grammar that Lean itself now checks.

## Representation Depth

The spine uses a native **semantic taxonomy** (`RepDepth` inductive in `Architecture.lean`),
enforced by `@[rep_depth <level>]` attributes and the `#audit_architecture` command.
The old numeric `L0`–`L5` labels are secondary; the primary grammar is semantic.

| `@[rep_depth ...]` | Presentation | Typical owners |
|---------------------|-------------|----------------|
| `count` | Count / relative-volume data | `RelativePotentialCountBridge` |
| `projective` | Projective / gauge / relative potential | `PositiveRayCore`, `RelativePotentialCore`, `RedLine` |
| `operator` | Operator / modular lift | `InformationPartitionCore`, `RelativeSurprisalOperatorLift` |
| `krein` | Krein / Clifford geometry | `SplitQuadratic`, `SplitQuadraticSheets`, `PolarizedSector` |
| `transport` | Transport / Bogoliubov frame change | `KreinDiracSpectralLift`, `SplitCliffordThermalBridge` |
| `thermo` | Thermodynamic / attention surfaces | `AttentionPolarizedSplit`, `AttentionPolarizedGibbsBridge`, `AttentionPolarizedSinkhornBridge` |

**Adjacency rule**: a non-`@[capstone]` declaration at depth `d` may only depend on
tagged declarations at depth `d` or `d − 1`. Capstones (`@[capstone]`) may span
multiple layers but must also carry a `@[rep_depth]` tag.

## Current Anchor Corridor

The deepest currently stabilized count-to-operator corridor is:
- [PositiveMeasure.lean](lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [RelativePotentialCountBridge.lean](lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- [RelativeSurprisalOperatorLift.lean](lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

Its new owner/cocycle seam is:
- `representativeMassShift` and `representativeMassShift_cocycle` at the representative level
- `countMassShift` and `countMassShift_cocycle` at the count specialization level
- `relativeCountModularPotentialOperator_cocycle` at the raw diagonal-operator level
- `relativeModularHamiltonian_sub_countMassShift_cocycle` at the averaged operator level

This is the current benchmark for what a nonvacuous adjacent corridor should look like in the repository.

## File Roles

Every stable file should be read as one of four roles:
- owner: defines the lowest natural surface for a presentation
- translator: moves one adjacent depth step
- coherence: proves that two adjacent composites agree
- capstone: consumes lower layers without defining new skip-level ontology

This role split is not just documentation style.
It is the repo's way of preserving one theory across several symmetric, operator, Krein, transport, and thermodynamic realizations without pretending they are the same file-level object.

The anti-facade rule is simple:
- a valid bridge file is either an adjacent translator or a real coherence file
- direct skip-level ontology is debt

In Lean-native terms, the current adjacency rules are:
- a tagged non-capstone declaration at depth `d` may only reach tagged declarations at depth `d` or `d − 1`
- a theorem that spans further must be explicitly tagged `@[capstone]` and carry a `@[rep_depth]` tag
- the `#audit_architecture` command in `Audit.lean` enforces this at build time

Additionally, a vacuity enforcement system classifies declarations by graph role:
- `@[infrastructure]`, `@[terminal]`, `@[expository]` — role tags checked by `Lint/Vacuity.lean`
- `tools/theorem_significance.py` — graph-level V0–V4 violations
- `tools/check_vacuity_policy.py` — CI gate

## What Is Actually Proved

The repo contains ~330 complete theorems (zero `sorry`). Approximately 85% are
definitional unfolding or single-step algebra. The remaining ~50 theorems carry
genuine mathematical content. This section inventories the substance honestly.

### Anchor corridor (count → projective → operator)

The corridor is a **coordinatization layer**: it tracks how normalization and
projectivization introduce a gauge shift, and proves the shift is a 1-cocycle.

Non-trivial results:
- `relativeLogDensity_mk_eq_representativeRelativeLogDensity_add_massShift`
  ([RelativePotentialCore](lean/InfoGeometry/Canonical/RelativePotentialCore.lean)):
  projective relative log-density = representative log-density + `log(Z ν / Z μ)`.
  The cocycle appears as a constant additive shift.
- `representativeMassShift_cocycle` / `countMassShift_cocycle`:
  the shift satisfies the Thompson 1-cocycle law.
- `relativeModularHamiltonian_sub_countMassShift_cocycle`
  ([RelativeSurprisalOperatorLift](lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)):
  the mass-shift-corrected modular Hamiltonian preserves rigid cocycle structure
  through the operator lift. This is the corridor's non-obvious theorem.

Proof methods: `field_simp`, `ring`. No hypotheses beyond positivity and full
support. No converse (recovering lower-layer data from the operator presentation)
is proved. No obstruction or classification.

### Krein / split-quadratic layer

First layer with proper functional analysis:
- `hasFDerivAt_potential` ([SplitQuadratic](lean/InfoGeometry/Krein/SplitQuadratic.lean)):
  Fréchet derivative of the indefinite quadratic potential, using `fderivInnerCLM`.
- `divergence_plusPoint_eq_half_sqdist` / `divergence_minusPoint_eq_neg_half_sqdist`
  ([SplitQuadraticSheets](lean/InfoGeometry/Krein/SplitQuadraticSheets.lean)):
  on the +1 eigensheet, signed Krein divergence collapses to Euclidean distance;
  on −1 it flips sign. Proves **opposite curvature** on opposite spectral sheets.
- `polarizedDivergence_nonneg` / `divergence_nonpos_of_mem_minusSheet`:
  sheet-wise convexity/concavity from eigenspace membership.

### Transport / Bogoliubov layer

Operator-algebraic results using Mathlib Banach-space calculus:
- `phaseAxisForce_eq_from_phaseAntilinearPart`
  ([BogoliubovTransport](lean/InfoGeometry/Canonical/BogoliubovTransport.lean)):
  all phase-axis transport comes from antilinear components only.
- `JBoost_add` / `epsilonBoost_add` / `KRotation_add`:
  additive time law for exponential flows via `NormedSpace.exp_add_of_commute`.
- `JBoost_comp_spectralPlusProj(t)`
  ([BogoliubovProjectorFlux](lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean)):
  hyperbolic rotation mixes spectral sheets — off-diagonal coupling as
  `sinh(t) · (P₋ ∘ J)`. Encodes Shale–Stinespring condition at operator level.
- `transportDirac_sq_eq_transportMetricOp`
  ([KreinDiracPolarizationBridge](lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean)):
  `(T·D·T⁻¹)² = T·g·T⁻¹` — Dirac-square law preserved under Bogoliubov conjugation.
- `transportObservable_isCocycle`
  ([WeylTransport](lean/InfoGeometry/Canonical/WeylTransport.lean)):
  two-point transport observable satisfies multiplicative cocycle law.

### Attention / thermo layer

- `gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights`
  ([AttentionPolarizedGibbsBridge](lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean)):
  Gibbs weight of polarized-split energy **equals** transformer attention weights.
  Formally proves attention is the canonical ensemble of a split-quadratic energy.
- `polarizedPlusAttentionWeights_eq_euclideanGibbsWeights_of_constantKeyNorm`:
  under fixed key norm, attention reduces to Euclidean Gibbs.

### Finite-dimensional generalized inverses

- [Singular.lean](lean/InfoGeometry/Canonical/Singular.lean) contains constructive
  Drazin and Moore–Penrose existence for finite-dimensional real Hilbert endomorphisms.

### Weyl / BdG corridor

- [TriadicWeylBridge](lean/InfoGeometry/Quantum/TriadicWeylBridge.lean) proves Weyl
  compatibility ↔ commutation with sheet sign operator ↔ vanishing projector fluxes.
- [RealBdG](lean/InfoGeometry/Canonical/RealBdG.lean) /
  [RealBdGSheetBridge](lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean) decompose
  lifted operators into K-linear and K-antilinear sectors.

## What Is Not Yet Proved

The following are **absent** from the current codebase. Any agent or document
claiming otherwise is wrong:

- **Converse / recovery**: no theorem recovers lower-layer data from upper-layer
  data. The corridor is one-directional (count → operator). Injectivity of the
  first-quantization map is not stated.
- **Obstruction theory**: no rigid obstruction, no classification of when a lift
  fails, no cohomological computation from the cocycles.
- **Uniqueness / rigidity**: no theorem asserts the cocycle or the lift is unique
  among possible bridges.
- **Spectral analysis**: eigenvalue analysis, spectral gaps, spectral rigidity
  are absent.
- **Infinite-dimensional extension**: all results are finite-dimensional.
- **Physical interpretation**: no theorem connects the formalism to a physical
  prediction. The attention–Gibbs bridge is structural, not empirical.
- **Riemannian geometry**: no metric, curvature tensor, geodesic, or Fisher
  information metric appears in the proved theorems.

The nucleus theorem that would validate the corridor as a theory (rather than
a coordinatization) is approximately:

> For finite positive count data, the projective relative potential determines
> a diagonal relative surprisal operator uniquely up to the normalization cocycle,
> and this lift is functorial under allowed adjacent translations.

The forward direction exists; uniqueness, converse, and functoriality are open.

## What Remains Open

The remaining work falls into three categories:

**Proof gaps** (mathematical substance):
- converse/recovery theorems for the count-to-operator lift
- functoriality of the cocycle-corrected modular Hamiltonian
- obstruction classification: when does a Bogoliubov transport fail to preserve
  the Dirac-square law?
- spectral consequences of the partition-function derivative
- Sinkhorn transport convergence and contraction bounds

**Packaging debt** (structural):
- theorem-shaped projections and Rosetta wrappers in some bridge files
- review-surface files still leaning on quarantined ontology
- declarations that are unconsumed owners vs. disposable packaging (the
  `generate_replacement_frontier.py` report distinguishes these)

**Infrastructure debt**:
- visualization: replacing hotspot-based coloring with depth-aware projector
- off-diagonal Bogoliubov group not yet on the stable path with implementability restriction
