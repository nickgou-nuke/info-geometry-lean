# Documentation map

> Status: `current authority`
> Source reviewed: 2026-11-03 at `214f7bcf733eaf4720913bc2c082936f2480d3fc`.
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
| [QMS-SOP-ALC-001 v4.1](ALCHEMICAL_QMS_SOP.md) | Quality Management System: role separation (G-A/A-A/QA-A/Orchestrator), Gate 0-5 pipeline, intent envelopes, audit telemetry, QA acceptance records, CAPA tracking |

## Mathematical source maps

| Topic | Read first |
|---|---|
| Main Lean library | [InfoGeometry.All](../lean/InfoGeometry/All.lean), [Lake targets](../lakefile.lean) |
| Operator algebra and Peirce constructions | [OperatorAlgebra guide](../lean/InfoGeometry/OperatorAlgebra/README.md), [Peirce archetype ledger](PEIRCE_OPERATOR_ARCHETYPES.md) |
| Categorical owners and finite-to-limit interfaces | [Categorical infrastructure map](CATEGORICAL_INFRASTRUCTURE_MAP.md) |
| CAR, Krein carriers, and projectivization | [Topic scope note](../README-CURRENT.md) |
| Nuclear operator parity, RPA, and phonon commutators | [Nuclear operator synthesis](NUCLEAR_OPERATOR_SYNTHESIS.md), [theorem contract](NUCLEAR_OPERATOR_PARITY_CONTRACT.md) |
| Two-sheeted operator transport and its remaining bridges | [Framework progress note](TWO_SHEETED_YANG_MILLS_FRAMEWORK_PROGRESS.md) |
| Souriau/Bost–Connes claims | [Transition status](SOURIAU_BOST_CONNES_TRANSITION_STATUS.md) |
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
- [QMS-SOP-ALC-001 v4.1](ALCHEMICAL_QMS_SOP.md) — Quality Management System with role separation and Gate 0-5 acceptance pipeline

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
- [Auto-Ontology agent operations](AUTO_ONTOLOGY_AGENT_OPERATIONS.md)
- [Repository ontology unification playbook](ONTOLOGY_UNIFICATION_PLAYBOOK.md)
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
