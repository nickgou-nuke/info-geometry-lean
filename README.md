# InfoGeometry Lean Fusion

> Status: `current authority`
> Audited: 2026-05-02
> Note: Maintained against the live code surface.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This repository has two live code surfaces:

- `lean/`: the Lean 4 theorem library and its architecture/audit layer
- `src/igf/` plus `tools/`: the Python CLI and repo tooling that build, validate,
  normalize, ingest, and report on generated graph artifacts

It also has a maintained generative-discovery layer:

- structured LLM dialogue and Socratic regeneration for theorem emergence
- packetized translation from symbolic generation into formal candidate work
- strict separation between generative ideation and proof authority
- a live Pauli auditor discipline that rejects inflated or underived closure

If prose and code disagree, trust the code.

## What Is Current

The current authority order is:

1. `lean/` and `lakefile.lean`
2. `src/igf/` and maintained scripts under `tools/`
3. `docs/CODEBASE_STATUS.md`
4. this file and the other maintained docs listed in `docs/README.md`

The repository is not a pure prose knowledge base. Most Markdown outside the
maintained entry docs is reference memory, archived handover material, or a
generated report snapshot.

## Live Repository Surface

Lean:

- package name: `infogeometry`
- main library entry: `lean/InfoGeometry.lean`
- full umbrella: `lean/InfoGeometry/All.lean`
- native audit/architecture anchors:
  - `lean/InfoGeometry/Audit.lean`
  - `lean/InfoGeometry/Meta/`

Python:

- package: `infogeometry`
- CLIs:
  - `igf` -> `src/igf/cli.py`
  - `infogeometry` -> `scripts.cli:main`
- maintained script lanes:
  - `tools/infra/`
  - `tools/frontier/`
  - `tools/docs/`
  - `tools/leantrail/`

Lake scripts defined in `lakefile.lean` include:

- `strictCheck`
- `dagStatus`
- `dagRefresh`
- `dagReports`
- `dagDoctor`
- `dagAll`
- `changedVerify`
- `leantrailConformance`
- `leantrailExport`
- `leantrailArangoIngest`
- `leantrailArangoPhysicsEval`
- `leantrailFailureHarvest`
- `leantrailPathLock`
- `leantrailHolePackets`

## Quick Start

Install Python tooling:

```bash
python3 -m venv .venv
. .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e .
```

Basic Lean-oriented checks:

```bash
lake script run changedVerify
lake script run dagStatus
lake script run dagDoctor
```

Whole DAG/report refresh:

```bash
lake script run dagAll
```

IGF pipeline CLI examples:

```bash
igf preflight
igf build --print-json
igf run --strict --print-json
igf validate --strict --print-json
```

## Repository Layout

- `lean/`
  Lean theorem sources
- `src/igf/`
  maintained Python package for artifact processing and Arango-backed workflows
- `tools/`
  operational scripts and compatibility wrappers
- `tests/`
  Python and Lean tests
- `docs/`
  maintained entry docs plus large reference-memory corpus
- `reports/`
  generated or point-in-time Markdown/JSON reports
- `artifacts/`
  generated outputs, snapshots, and run payloads
- `archive/`
  historical material kept for provenance
- `handover/`
  packet and runbook history, not current authority

## Documentation Rules

Start with:

- [docs/README.md](docs/README.md)
- [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)
- [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md)
- [docs/ModuleMap.md](docs/ModuleMap.md)
- [docs/OperationalIntent.md](docs/OperationalIntent.md)
- [docs/GenerativeDiscoveryArchitecture.md](docs/GenerativeDiscoveryArchitecture.md)
- [docs/FormalizationDiscipline.md](docs/FormalizationDiscipline.md)
- [docs/ARANGO_DAG_REFRESH_METHODOLOGY.md](docs/ARANGO_DAG_REFRESH_METHODOLOGY.md)
- [PAULI_MANDATE.md](PAULI_MANDATE.md)
- [Installation.md](Installation.md)
- [NEWCOMER_PATH.md](NEWCOMER_PATH.md)

Do not treat old reports, synthesis notes, or handover packets as live state
unless they have been regenerated or explicitly re-audited.

`docs/black_books/` is intentionally protected exploration material and is not
rewritten by the Markdown cleanup lane.

## Current Audit Note

This README was rewritten on 2026-05-02 to match the current code surface.
During that pass, the repository was observed to have a dirty working tree with
active Lean and Python changes already in progress. This documentation refresh
does not claim a fresh green build; see [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)
for the current verified status language.
