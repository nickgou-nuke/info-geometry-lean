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

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4
proofs is the repository's highest proof-engineering priority.

All agents and skills must follow
[docs/CONSTRUCTIVE_CLOSURE_MANDATE.md](docs/CONSTRUCTIVE_CLOSURE_MANDATE.md):
witness packets, certificate fields, external certificates, assumption
interfaces, graph edges, literature citations, and physics analogies are closure
debt until discharged by kernel-checked Lean proofs or imported mathlib
theorems. No anonymous witnesses and no promotion of unformalized sockets.

The formula/function rule is also current policy:
[docs/FORMULA_FUNCTION_POLICY.md](docs/FORMULA_FUNCTION_POLICY.md).
Formulas are definitions, functions are functions, and downstream code must
call the function directly rather than storing the formula as prose or a field
label.

## What Is Current

The current authority order is:

1. `lean/` and `lakefile.lean`
2. `src/igf/` and maintained scripts under `tools/`
3. `docs/CODEBASE_STATUS.md`
4. this file and the other maintained docs listed in `docs/README.md`

The repository is not a pure prose knowledge base. Most Markdown outside the
maintained entry docs is reference memory, archived handover material, or a
generated report snapshot.

## Beehive / Swarm Architecture

The local-first swarm / beehive layer is documented in the maintained docs.
Use these as the current design map for agent orchestration, provider routing,
and long-running worker layout:

- [docs/README.md](docs/README.md)
- [docs/hive_greenfield_architecture.md](docs/hive_greenfield_architecture.md)
- [docs/hive_migration_plan.md](docs/hive_migration_plan.md)
- [docs/hive_beehive_implementation_checklist.md](docs/hive_beehive_implementation_checklist.md)
- [docs/hive_beehive_operator_runbook.md](docs/hive_beehive_operator_runbook.md)
- [docs/hive_beehive_systemd_units.md](docs/hive_beehive_systemd_units.md)
- [docs/hive_beehive_overrides.md](docs/hive_beehive_overrides.md)
- [scripts/install_hive_beehive_systemd_units.sh](scripts/install_hive_beehive_systemd_units.sh)
- [scripts/uninstall_hive_beehive_systemd_units.sh](scripts/uninstall_hive_beehive_systemd_units.sh)
- [docs/hive_graph_resident_os.md](docs/hive_graph_resident_os.md)
- [docs/hermes_recursive_hive_architecture.md](docs/hermes_recursive_hive_architecture.md)
- [docs/hive_neural_backbone_architecture.md](docs/hive_neural_backbone_architecture.md)
- [docs/hive_beehive_swarm_implementation_plan.md](docs/hive_beehive_swarm_implementation_plan.md)

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

## GraphRAG Explorer

Use the unified natural-language explorer to search Lean declarations, docs, black books, handover material, and external mirrors:

```bash
python3 tools/infra/graph_rag_query.py "Weyl character formula" --top-k 8
python3 tools/infra/graph_rag_query.py "Weyl character formula" --top-k 8 --no-gravity --format json
```

The explorer is retrieval-only for prose and external mirrors; Lean remains the proof authority.

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

## Closure-Debt Constructive-Proof SOP

Use this SOP when reducing closure debt in Lean modules.

1. Run deterministic debt discovery first

```bash
python3 tools/quality/closure_debt_crawler.py \
  --root lean \
  --json-out reports/audit/repo-closure-debt-crawler.json \
  --md-out reports/audit/repo-closure-debt-crawler.md \
  --print-summary

python3 tools/quality/placeholder_audit.py \
  --root lean/InfoGeometry \
  --json-out reports/audit/repo-placeholder-audit.json \
  --md-out reports/audit/repo-placeholder-audit.md \
  --signals-out reports/audit/repo-placeholder-signals.json
```

For agentic file-by-file audit, run the resumable wrapper. It invokes
`closure_debt_crawler.py` once per Lean file and passes each generated prompt to
the configured coding agent:

```bash
python3 tools/quality/run_agentic_closure_debt_audit.py \
  --root lean \
  --coding-agent-command 'codex exec --json' \
  --out-dir reports/audit/agentic-closure-debt \
  --print-progress
```

Smoke run:

```bash
python3 tools/quality/run_agentic_closure_debt_audit.py \
  --root lean \
  --coding-agent-command 'codex exec --json' \
  --limit 1 \
  --print-progress
```

This is an audit lane, not a proof lane. The agent reports gaps and repair
strategies; closing a gap still requires Lean edits and successful targeted
`lake env lean` / `lake build`.

2. Prioritize work in this order
- P0: hard findings (`sorry`, `admit`, unsafe proof holes)
- P1: owner-target propositions that currently lack theorem-backed constructive chains
- P2: soft/advisory debt (skeletal proofs, packaging debt)

3. Enforce proof authority policy
- No witness placeholders as final authority.
- Green compile is necessary but not sufficient.
- Every promoted proposition must be backed by explicit derivation notes: target theorem -> local lemmas -> upstream owner lemmas -> mathlib roots.
- Prefer existing mathlib lemmas first; if missing, add minimal intermediate lemmas in-repo with full proofs.
- External literature (AFP/arXiv/etc.) is input for theorem design only; authority is Lean+mathlib-checked proof terms.
- Reject vacuous packaging as closure evidence (`Nonempty`, `Exists`, `_valid` projection-only readbacks, interface/witness shells) unless fully discharged by theorem derivation.

4. Verify each touched module immediately

```bash
lake env lean lean/<Path/To/Module>.lean
lake build <Module.Name>
```

5. Re-run debt scanners after each batch and record artifacts
- Keep JSON/MD outputs under `reports/audit/` for each pass.
- Do not claim debt reduction without scanner evidence and green Lean build evidence.

6. Commit discipline
- Keep commits surgical (module + directly related tests/scripts only).
- If asked to push, push both remotes (`origin` and `upstream`).

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

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
