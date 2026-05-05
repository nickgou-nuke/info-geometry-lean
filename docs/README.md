# Documentation Map

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

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

## Maintained Entry Docs

Use these first:

- [../README.md](../README.md)
- [CODEBASE_STATUS.md](CODEBASE_STATUS.md)
- [RepositoryMemoryMap.md](RepositoryMemoryMap.md)
- [ModuleMap.md](ModuleMap.md)
- [OperationalIntent.md](OperationalIntent.md)
- [GenerativeDiscoveryArchitecture.md](GenerativeDiscoveryArchitecture.md)
- [FormalizationDiscipline.md](FormalizationDiscipline.md)
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
8. [../PAULI_MANDATE.md](../PAULI_MANDATE.md)
9. [../Installation.md](../Installation.md)
10. [../NEWCOMER_PATH.md](../NEWCOMER_PATH.md)
11. [OperatorQuickstart.md](OperatorQuickstart.md)
12. [DAGTroubleshooting.md](DAGTroubleshooting.md)
13. [LeanTrail.md](LeanTrail.md)

## What Changed In This Audit

On 2026-05-02, the Markdown corpus was reclassified so old notes and generated
reports stop presenting themselves as current repository truth. Black Book
chapters were left untouched.
