# Documentation map

> Status: `current authority`
> Source reviewed: 2026-11-15 at [`abd5826b3676`](https://github.com/nickgou-nuke/info-geometry-lean/commit/abd5826b3676fab6231c66b646ec1cc5aeed6732)
> plus scoped working-tree kernel verification of
> [`InfoGeometry.Foundations.InfoGeometryCoreLibrary`](../lean/InfoGeometry/Foundations/InfoGeometryCoreLibrary.lean) and
> [`InfoGeometry.OperatorAlgebra.PeirceBiSandwich.All`](../lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/All.lean).
> Scope: maintained entry points and source routing. Linked research notes and
> historical reports retain their own scope and verification dates.

Start with the [project README](../README.md),
[getting-started guide](GETTING_STARTED.md), and [AGENTS.md](../AGENTS.md).
For mathematical or implementation questions, use the
[deep-search protocol](REPO_DEEP_SEARCH_PROTOCOL.md) and inspect actual source.
An index entry, graph relation, or filename does not establish a theorem.

## Maintained operating guides

| Guide | Role |
|---|---|
| [AGENTS.md](../AGENTS.md) | Source authority, proof acceptance, ownership, build serialization, and dependency preservation |
| [Getting started](GETTING_STARTED.md) | Checkout, pinned dependencies, and scoped validation commands |
| [Canonical pipeline](CANONICAL_AGENT_PIPELINE.md) | Implementation-backed commands and optional runtime prerequisites |
| [Hive agent commandments](HIVE_AGENT_COMMANDMENTS.md) | Compact operating checklist subordinate to root policy |
| [Deep-search protocol](REPO_DEEP_SEARCH_PROTOCOL.md) | Multi-lane discovery and precise absence/novelty claims |
| [Cache policy](../WARNING_DO_NOT_RUN_CACHE.md) | Cache preservation and the build helper's hydration behavior |
| [Markdown governance](MarkdownCorpusGovernance.md) | Documentation status, provenance, and evidence requirements |
| [Source audit, 2026-11-03](DOCUMENTATION_SOURCE_AUDIT_2026-11-03.md) | Bounded source findings, baseline CI evidence, and remaining integration limitations |

## Mathematical source maps

| Topic | Read first |
|---|---|
| Main Lean library & core foundations | [InfoGeometryCoreLibrary](../lean/InfoGeometry/Foundations/InfoGeometryCoreLibrary.lean), [InfoGeometry.All](../lean/InfoGeometry/All.lean), [Lake targets](../lakefile.lean) |
| Peirce bi-sandwich suite & umbrella synthesis | [PeirceBiSandwich.All](../lean/InfoGeometry/OperatorAlgebra/PeirceBiSandwich/All.lean), [OperatorAlgebra guide](../lean/InfoGeometry/OperatorAlgebra/README.md), [Peirce archetype ledger](PEIRCE_OPERATOR_ARCHETYPES.md) |
| Statistical manifolds & information geometry (Pillar I) | [ParametricCramerRao](../lean/InfoGeometry/InformationGeometry/ParametricCramerRaoAndCumulants.lean), [CsiszarAlphaDivergence](../lean/InfoGeometry/InformationGeometry/CsiszarAlphaDivergenceAndChentsovMonotonicity.lean), [EguchiMetrics](../lean/InfoGeometry/InformationGeometry/EguchiMetricsAndDualFlatCurvature.lean) |
| Categorical Markov categories & colimits (Pillar III) | [MarkovCategoryAndColimitInformation](../lean/InfoGeometry/Categorical/MarkovCategoryAndColimitInformation.lean), [MarkovComonoidAndBlackwellSufficiency](../lean/InfoGeometry/Categorical/MarkovComonoidAndBlackwellSufficiency.lean), [Categorical infrastructure map](CATEGORICAL_INFRASTRUCTURE_MAP.md) |
| Quantum information & monotone metrics (Pillars II & IV) | [KadisonSchwarzAndQuantumCramerRao](../lean/InfoGeometry/OperatorAlgebra/KadisonSchwarzAndQuantumCramerRao.lean), [GNSRepresentationAndPetzMonotoneMetrics](../lean/InfoGeometry/OperatorAlgebra/GNSRepresentationAndPetzMonotoneMetrics.lean) |
| Krein–Peirce–Kitaev operator bridges | [NoncommutativeKreinMathlibBridge](../lean/InfoGeometry/Algebra/NoncommutativeKreinMathlibBridge.lean), [KreinPeirceTowerIntertwine](../lean/InfoGeometry/Algebra/KreinPeirceTowerIntertwine.lean), [PeirceTetraktysKreinBridge](../lean/InfoGeometry/Algebra/PeirceTetraktysKreinBridge.lean), [KitaevPeirceAporiaEpistemicSynthesis](../lean/InfoGeometry/Algebra/KitaevPeirceAporiaEpistemicSynthesis.lean) |
| Modular GKSL & quantum Spohn thermodynamics | [GKSLDissipationIdentity](../lean/InfoGeometry/Modular/GKSLDissipationIdentity.lean), [GKSLGibbsAndDuallyFlatSpinCumulants](../lean/InfoGeometry/Modular/GKSLGibbsAndDuallyFlatSpinCumulants.lean), [WeldedBlochQuantumSpohnSynthesis](../lean/InfoGeometry/Modular/WeldedBlochQuantumSpohnSynthesis.lean), [BlochBallUmegakiAndQuantumSpohn](../lean/InfoGeometry/Modular/BlochBallUmegakiAndQuantumSpohn.lean), [SchrodingerGKSLFlowBridge](../lean/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean) ([src/ mirror](../src/InfoGeometry/Modular/SchrodingerGKSLFlowBridge.lean)), [AnisotropicBKMHessianAndMultiQubitSpohn](../lean/InfoGeometry/Modular/AnisotropicBKMHessianAndMultiQubitSpohn.lean) |
| Graded Clifford superbase & entanglement rank | [Cl11SuperBaseAndEntanglementRank](../lean/InfoGeometry/Clifford/Cl11SuperBaseAndEntanglementRank.lean) |
| Unbounded resolvent flows & C₀-group generators | [TripotentUnboundedResolventFlow](../lean/InfoGeometry/OperatorAlgebra/TripotentUnboundedResolventFlow.lean), [UnboundedHilbertResolventAndC0GroupWitness](../lean/InfoGeometry/OperatorAlgebra/UnboundedHilbertResolventAndC0GroupWitness.lean) |
| Lattice gauge projections & Elitzur's theorem | [ElitzurLatticeGaugeProjection](../lean/InfoGeometry/OperatorAlgebra/ElitzurLatticeGaugeProjection.lean), [NLinkElitzurChainAndCompactU1Gauge](../lean/InfoGeometry/OperatorAlgebra/NLinkElitzurChainAndCompactU1Gauge.lean) |
| UHF C*-algebra inductive limit completion | [UHFColimitCStarCompletion](../lean/InfoGeometry/Algebra/UHFColimitCStarCompletion.lean) |
| Discrete Cantor Fourier uncertainty principle | [DiscreteCantorFourierUncertainty](../lean/InfoGeometry/Algebra/DiscreteCantorFourierUncertainty.lean) |
| Continuous $L^2([0,1])$ Cantor FUP contraction | [ContinuousL2CantorFourierUncertainty](../lean/InfoGeometry/Analysis/ContinuousL2CantorFourierUncertainty.lean) |
| Nondegenerate Krein signature (5,5) bridge | [Pin55NondegenerateKreinBridge](../lean/InfoGeometry/Lie/Pin55NondegenerateKreinBridge.lean) |
| Global $SO(5,5)$ & conformal 3-grading precursors | [SO55GlobalConformalPrecursors](../lean/InfoGeometry/Lie/SO55GlobalConformalPrecursors.lean) |
| Weyl–Cartan split & Iwasawa KAN polar equivariance | [WeylCartanKANPolarEquivariance](../lean/InfoGeometry/Algebra/WeylCartanKANPolarEquivariance.lean), [NoncommutativeWeylCartanKANPolarEquivariance](../lean/InfoGeometry/Algebra/NoncommutativeWeylCartanKANPolarEquivariance.lean), [WeylTraceKANPolarEquivariance](../lean/InfoGeometry/Canonical/WeylTraceKANPolarEquivariance.lean), [ComplexSL2IwasawaAndHyperbolicPolar](../lean/InfoGeometry/Algebra/ComplexSL2IwasawaAndHyperbolicPolar.lean) |
| Hilbert boundary sewn anomaly cancellation & Cuntz O₂ | [ConcreteHilbertSewnAnomaly](../lean/InfoGeometry/Canonical/ConcreteHilbertSewnAnomaly.lean), [ConcreteHilbertCuntzO2](../lean/InfoGeometry/Canonical/ConcreteHilbertCuntzO2.lean) |
| Lattice OS transfer semigroup & mass gap precursors | [OsterwalderSchraderTransferSemigroupAndMassGap](../lean/InfoGeometry/OperatorAlgebra/OsterwalderSchraderTransferSemigroupAndMassGap.lean) |
| Constructive Chebyshev prime bounds & Hoeffding tail | [ChebyshevPrimeAndHoeffdingBounds](../lean/InfoGeometry/Arithmetic/ChebyshevPrimeAndHoeffdingBounds.lean) |
| Logarithmic integral $\mathrm{li}(x)$ & $\zeta$ pole precursors | [RiemannZetaLogarithmicIntegralPrecursors](../lean/InfoGeometry/Arithmetic/RiemannZetaLogarithmicIntegralPrecursors.lean) |
| Solve et Coagula noncommutative causal poset | [SolveEtCoagulaPeirceAporiaPoset](../lean/InfoGeometry/OperatorAlgebra/SolveEtCoagulaPeirceAporiaPoset.lean) |
| Nuclear operator parity, RPA, and phonon commutators | [Nuclear operator synthesis](NUCLEAR_OPERATOR_SYNTHESIS.md), [theorem contract](NUCLEAR_OPERATOR_PARITY_CONTRACT.md) |
| Two-sheeted operator transport and framework progress | [Framework progress note](TWO_SHEETED_YANG_MILLS_FRAMEWORK_PROGRESS.md) |
| Open debt problems & constructive closure | [Open debt problems](OPEN_DEBT_PROBLEMS.md) |
| Souriau/Bost–Connes claims | [Transition status](SOURIAU_BOST_CONNES_TRANSITION_STATUS.md) |
| CAR, Krein carriers, and projectivization | [Topic scope note](../README-CURRENT.md) |
| Owner/translator separation | [Bilingual spine policy](BILINGUAL_SPINE_POLICY.md) |

Read each map's stated revision and follow it to the owner declarations,
imports, and consumers. Distinguish a supplied interface from an inhabited
model, a compatible cone from a universal colimit, and an algebraic identity
from an additional analytic or physical interpretation.

## Proof discipline and review

- [Constructive closure mandate](CONSTRUCTIVE_CLOSURE_MANDATE.md)
- [Formula/function policy](FORMULA_FUNCTION_POLICY.md)
- [Formalization discipline](FormalizationDiscipline.md)
- [Independent agent audit SOP](INDEPENDENT_AGENT_AUDIT_SOP.md)
- [Generated-artifact policy](GeneratedArtifactsPolicy.md)
- [Open debt problems](OPEN_DEBT_PROBLEMS.md)

Native proofs establish their stated conditional conclusions. Unproved witness
existence, certificate discharge, or carrier-identification obligations must
remain visible as separate debt. A narrow compilation result must not be
reported as verification of the whole repository or a proposed physical theory.

## Tooling and configured services

- [Tools overview](../tools/README.md)
- [Infrastructure guide](../tools/infra/README.md)
- [Documentation tools](../tools/docs/README.md)
- [LeanTrail guide](../leantrail/README.md)
- [LeanTrail topic documentation](LeanTrail.md)
- [AST/AQL/hash navigation](ASTAQLHASH-HOWTO.md)
- [Arango refresh methodology](ARANGO_DAG_REFRESH_METHODOLOGY.md)
- [aiClaw review runbook](AICLAW_CHATGPT_REVIEW_RUNBOOK.md)
- [Pi agent-team operations](PI_AGENT_TEAMS_OPERATIONS.md)
- [AI Studio transcript export](AI_STUDIO_TRANSCRIPT_EXPORT.md)

These guides route to source and configured services. They do not establish
that a service is running or that an imported graph matches the current
revision. The canonical pipeline records the known Pi/Archon prerequisites;
the infra guide records local DAG configuration requirements.

## Additional inventories and topic ledgers

The following documents are useful discovery inputs. Their dates, source
revisions, and generated-artifact provenance must be checked before treating
counts, completion claims, or operational commands as current:

- [Codebase status](CODEBASE_STATUS.md)
- [Repository memory map](RepositoryMemoryMap.md)
- [Module map](ModuleMap.md)
- [Operational intent](OperationalIntent.md)
- [Generative discovery architecture](GenerativeDiscoveryArchitecture.md)
- [Tooling methodology](ToolingMethodology.md)
- [Induction systematics](InductionSystematics.md)
- [Induction how-to](InductionHowTo.md)
- [Kasparov/Krein/DIII runbook](KASPAROV_KREIN_DIII_RUNBOOK.md)
- [Kasparov/Krein/DIII ledger](KASPAROV_KREIN_DIII_LEDGER.md)
- [Topology/projective closure ledger](TOPOLOGY_PROJECTIVE_CLOSURE_LEDGER.md)
- [Evidence ledger](EVIDENCE_LEDGER.md)

## Research history and deployment plans

Long research transcripts, design targets, old task briefs, and generated
reports are preserved for provenance. They can contain proposed Lean code,
earlier interfaces, or interpretations superseded by current owners.

- [Universal grade-generator transcript](../AGENTS-Universal-Grade-Generator.md)
- [Two-sheeted research transcript](../Two-Sheeted-Yang-Mills-Inductive-Colimit.md)
- [Historical research review](reviews/2026-10-21-research-and-agent-accessibility.md)
- [Historical CAS task brief](../PROJECT.md)
- [Historical seven-stage synthesis](../REPOCONTENT.md)
- [Hive architecture](hive_greenfield_architecture.md), [migration plan](hive_migration_plan.md), and [operator runbook](hive_beehive_operator_runbook.md)
- [Archived installation guide](root-archive/Installation.md)
- [Archived newcomer path](root-archive/NEWCOMER_PATH.md)
- [Archived Pauli mandate](root-archive/PAULI_MANDATE.md)

Use [Getting started](GETTING_STARTED.md) for the maintained setup route. The
archived guides above are not substitutes for current dependency checks.

## Corpus status and protected content

Follow [Markdown governance](MarkdownCorpusGovernance.md) for status labels.
The protected `docs/black_books/` and `docs/black_books_refactor/` research
collections are excluded from cleanup rewrites. Generated documents under
`docs/auto/`, `reports/`, and artifact directories require their generation
revision and inputs before reuse. A generation timestamp is not a semantic
review date.
