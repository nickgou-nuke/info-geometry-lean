# Documentation Map

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This file is stale as an authority source. Use it only as a routing map and
re-audit against the live code surface before relying on any claim.

This directory is mixed on purpose.

Only a small subset is maintained as current operational documentation. Most
other Markdown here is reference memory, research synthesis, backlog, or
historical thinking that must be re-audited against code before use.

## Documentation Philosophy

We turned the docs from a Markdown heap into an epistemic routing system.

We did not just clean up prose. We rewrote the documentation as an authority
system that distinguishes live guidance from reference memory, generated
reports, archive, and handover material, so a reader can tell what to trust
first.

The maintained front door now runs through:

- `README.md`
- `docs/README.md`
- `docs/CODEBASE_STATUS.md`
- `docs/ModuleMap.md`
- `docs/OperationalIntent.md`
- `docs/ToolingMethodology.md`
- `docs/FORMULA_FUNCTION_POLICY.md`
- `NEWCOMER_PATH.md`

Those docs describe the repository as three coupled systems at once:

- a Lean theorem library
- an artifact, graph, and tooling system
- a generative discovery machine with strict closure gates

The project can still speak in its full physics, information-geometric, and
analytic-psychology language, but now every claim has a lane, a status, an
authority level, and a route back to code, artifact, or proof.

If documentation and code disagree, trust:

1. `lean/` and `lakefile.lean`
2. `src/igf/` and maintained scripts under `tools/`
3. [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
4. the maintained docs listed below

## Constructive Closure Mandate

[CONSTRUCTIVE_CLOSURE_MANDATE.md](CONSTRUCTIVE_CLOSURE_MANDATE.md) is current
policy for all repo agents, skills, proof workflows, and closure-debt audits.
Replacing witness-gated and external-certificate leftovers with native Lean 4
proofs is the highest mandate. Unformalized witnesses, certificates,
literature references, physics analogies, and graph edges remain closure debt
until discharged by kernel-checked Lean or mathlib proofs.

[FORMULA_FUNCTION_POLICY.md](FORMULA_FUNCTION_POLICY.md) is current policy for
definitional formulas. Formulas must be plain functions, not prose labels or
field aliases, and downstream code must call them directly.

## Maintained Entry Docs

Use these first:

- [../README.md](../README.md)
- [CONSTRUCTIVE_CLOSURE_MANDATE.md](CONSTRUCTIVE_CLOSURE_MANDATE.md)
- [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [ModuleMap.md](ModuleMap.md)
- [OperationalIntent.md](OperationalIntent.md)
- [GenerativeDiscoveryArchitecture.md](GenerativeDiscoveryArchitecture.md)
- [FormalizationDiscipline.md](FormalizationDiscipline.md)
- [InductionSystematics.md](InductionSystematics.md)
- [InductionHowTo.md](InductionHowTo.md)
- [../PAULI_MANDATE.md](../PAULI_MANDATE.md)
- [GeneratedArtifactsPolicy.md](GeneratedArtifactsPolicy.md)
- [MarkdownCorpusGovernance.md](MarkdownCorpusGovernance.md)
- [MaldacenaLectureTheoremMap.md](MaldacenaLectureTheoremMap.md)
- [ToolingInventory.md](ToolingInventory.md)
- [OperatorQuickstart.md](OperatorQuickstart.md)
- [DAGTroubleshooting.md](DAGTroubleshooting.md)
- [LeanTrail.md](LeanTrail.md)
- [../Installation.md](../Installation.md)
- [../NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
- [../tools/README.md](../tools/README.md)
- [../tools/infra/README.md](../tools/infra/README.md)
- [../leantrail/README.md](../leantrail/README.md)

## Beehive Architecture Docs

These are the current design target for the local-first swarm / beehive layer.
They are not theorem authority, but they are the best map for the runtime:

- [hive_greenfield_architecture.md](hive_greenfield_architecture.md)
- [hive_migration_plan.md](hive_migration_plan.md)
- [hive_beehive_implementation_checklist.md](hive_beehive_implementation_checklist.md)
- [hive_beehive_operator_runbook.md](hive_beehive_operator_runbook.md)
- [hive_beehive_systemd_units.md](hive_beehive_systemd_units.md)
- [hive_beehive_overrides.md](hive_beehive_overrides.md)
- [../scripts/install_hive_beehive_systemd_units.sh](../scripts/install_hive_beehive_systemd_units.sh)
- [../scripts/uninstall_hive_beehive_systemd_units.sh](../scripts/uninstall_hive_beehive_systemd_units.sh)
- [hive_graph_resident_os.md](hive_graph_resident_os.md)
- [hermes_recursive_hive_architecture.md](hermes_recursive_hive_architecture.md)
- [hive_neural_backbone_architecture.md](hive_neural_backbone_architecture.md)
- [hive_beehive_swarm_implementation_plan.md](hive_beehive_swarm_implementation_plan.md)

## Reference Notes

These are useful routing notes, but they are not current authority:

- [gromov_jaynes_probability_note.md](gromov_jaynes_probability_note.md)

## Protected Markdown

These paths are intentionally excluded from content-rewrite cleanup:

- `docs/black_books/`
- `docs/black_books_refactor/`

They may still be linked, but they are not auto-rewritten into repository
policy.

## Status Classes

- `current authority`
  Maintained entry docs that describe the live codebase
- `maintained local guide`
  Current for a subsystem, but subordinate to repo-wide authority docs
- `reference memory`
  Potentially useful notes that are not current authority
- `generated/historical report`
  A report snapshot that must be regenerated before use
- `archival reference`
  Kept for provenance or archaeology
- `historical handover`
  Packet/runbook history, not current policy

## Generated Documentation

The only script-owned doc surface under `docs/` is:

- `docs/auto/`

Its maintained generators live under:

- `tools/docs/`

Generated Markdown also appears heavily under:

- `reports/`
- selected artifact/run directories

Do not hand-curate those surfaces as if they were source of truth.

## Practical Reading Order

1. [../README.md](../README.md)
2. [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
3. [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
4. [ModuleMap.md](ModuleMap.md)
5. [OperationalIntent.md](OperationalIntent.md)
6. [GenerativeDiscoveryArchitecture.md](GenerativeDiscoveryArchitecture.md)
7. [FormalizationDiscipline.md](FormalizationDiscipline.md)
8. [InductionSystematics.md](InductionSystematics.md)
9. [InductionHowTo.md](InductionHowTo.md)
10. [../PAULI_MANDATE.md](../PAULI_MANDATE.md)
9. [../Installation.md](../Installation.md)
10. [../NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
11. [OperatorQuickstart.md](OperatorQuickstart.md)
12. [DAGTroubleshooting.md](DAGTroubleshooting.md)
13. [LeanTrail.md](LeanTrail.md)
14. [black_books/231_the_moebius_topology_of_information.md](black_books/231_the_moebius_topology_of_information.md)

## What Changed In This Audit

On 2026-05-02, the Markdown corpus was reclassified so old notes and generated
reports stop presenting themselves as current repository truth. Black Book
chapters were left untouched.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate temporary scaffolding (Native Closure Mandated: Closure Debt)

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate field (Native Closure Mandated: Closure Debt)s, external certificates, and assumption interfaces are temporary temporary scaffolding (Native Closure Mandated: Closure Debt) only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
