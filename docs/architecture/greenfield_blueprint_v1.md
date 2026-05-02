# Greenfield Blueprint v1 (Info-Geometry Lean Fusion)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../../README.md), [docs/README.md](../README.md), [docs/CODEBASE_STATUS.md](../CODEBASE_STATUS.md)

This is a clean-room rebuild specification for the Info-Geometry Lean Fusion
toolchain. It keeps the current doctrine, but removes drift between scripts,
schemas, run identities, Arango queries, and proof-authority boundaries.

## 0. North-Star Architecture

Hard authority split:

- Lean is the truth kernel: theorems, proofs, and formal semantics.
- ArangoDB is derived navigation and provenance memory.
- Heuristic and generative lanes are proposal-only and never proof authority.

Non-negotiables:

- verification-first development;
- auth enabled by default;
- deterministic artifacts;
- schema-versioned boundaries;
- proof-carrying escalation only;
- no overclaim across lanes.

## 1. Repository Layout

Target greenfield layout:

```text
repo/
  pyproject.toml
  README.md
  docs/
    architecture/
      00_principles.md
      01_lane_boundaries.md
      02_claim_safety.md
    schemas/
    runbooks/
  schemas/
    ig_patch_run.v1.json
    ig_chiral_patch.v1.json
    ig_patch_member.v1.json
    ig_patch_edge.v1.json
    ig_patch_spectral_signature.v1.json
  src/igf/
    config/
      model.py
      loader.py
      env_aliases.py
      preflight.py
    pipeline/
      build.py
      validate.py
      ingest.py
      verify.py
      report.py
      orchestrator.py
    graph/
      arango_client.py
      migrations.py
      collections.py
      indexes.py
      query_registry.py
      query_runner.py
    artifacts/
      io.py
      serializers.py
      schema_validate.py
      compatibility_adapters.py
    policy/
      claim_scope.py
      lane_tags.py
      enforcement.py
    lean/
      authority_bridge.py
      theorem_linking.py
  cli/
    igf.py
  tests/
    unit/
    contract/
    integration/
    regression/
    fixtures/
      golden/
  migrations/
    arango/
    artifact/
    query/
  tools/
    dev/
      bootstrap.sh
      smoke.sh
```

The current repository can migrate toward this layout incrementally. Existing
scripts should first become wrappers around `src/igf` library modules, then be
deprecated after CI uses the unified CLI.

## 2. Canonical Data Contracts

### 2.1 Global Identity Policy

- `run_id` is canonical across all artifacts and Arango collections.
- `_key` may differ for storage reasons, but `run_id` is always present and
  authoritative.
- No verification query may derive run identity from `_key` prefix matching.
- Joins use `run_id` and `patch_id`, never string-prefix hacks.

### 2.2 Required Fields

`ig_patch_runs`:

- `_key`
- `run_id`
- `schema_version`
- `created_at`
- `source_graph_hash`
- `algorithm_version`

`ig_chiral_patches`:

- `_key`
- `patch_id`
- `run_id`
- `schema_version`
- `patch_type`
- `node_count`
- `edge_count`
- `chiral_entropy`
- `claim_scope`
- `non_overclaim`

`ig_patch_spectral_signatures`:

- `_key`
- `patch_id`
- `run_id`
- `schema_version`
- `eigenvalues`
- `nullity`
- `pseudo_logdet`

`ig_patch_members`:

- `_from`
- `_to`
- `patch_id`
- `run_id`
- `schema_version`
- `membership_type`

`ig_patch_edges`:

- `_from`
- `_to`
- `from_patch_id`
- `to_patch_id`
- `run_id`
- `schema_version`
- `edge_type`

### 2.3 Schema Enforcement

- Validate JSON schemas before writing artifacts.
- Validate JSON schemas before ingesting artifacts.
- Add contract tests for every supported schema version.
- Compatibility adapters must be explicit by version.
- Avoid implicit "best effort" field guessing in production paths.

## 3. Unified CLI And Pipeline Kernel

One CLI should drive the graph sidecar lane:

```text
igf preflight
igf build
igf validate
igf ingest
igf verify
igf report
igf run
```

Example invocations:

```bash
igf run --profile local --run-id auto
igf validate artifacts/ --strict
igf verify --run-id <id> --json
```

Exit code policy:

- `0`: success;
- `1`: runtime, auth, network, or schema failure;
- `2`: semantic/verdict regression mismatch.

The CLI should be thin. The durable behavior belongs in `src/igf`.

## 4. Config And Environment Model

Use one typed config object for:

- Arango endpoint;
- database;
- username;
- password;
- lane toggles;
- artifact paths;
- strictness flags.

Alias normalization belongs in one module only:

- `ARANGO_USER` or `ARANGO_USERNAME`;
- `ARANGO_PASS` or `ARANGO_PASSWORD`.

`igf preflight` checks:

- credentials are present;
- endpoint is reachable;
- database exists;
- required collections exist;
- required indexes exist;
- schema versions are compatible.

## 5. Arango Layer Design

### 5.1 Collection And Index Registry

- Declare collections and indexes in one registry.
- Migrations create or update them idempotently.
- Index creation tolerates already-existing indexes.
- Auth is on by default in integration tests.

### 5.2 Query Registry

- All AQL queries live in `query_registry.py` or versioned `.aql` files.
- Operational scripts should not embed one-off AQL strings.
- Each query has:
  - a stable query ID;
  - an input contract;
  - an output contract;
  - a fixture-backed test.

### 5.3 Verification Queries

`verify_latest_summary(run_id?)` should:

- prefer an explicit `run_id`;
- fall back to the latest `ig_patch_runs.run_id`;
- count children by `run_id` and `patch_id` joins;
- avoid `_key` prefix assumptions.

## 6. Deterministic Pipeline Stages

### Stage A: Build

Inputs:

- `ig_nodes.jsonl`;
- `ig_edges.jsonl`;
- optional fingerprints.

Outputs:

- `ig_patch_runs.jsonl`;
- `ig_chiral_patches.jsonl`;
- `ig_patch_members.jsonl`;
- `ig_patch_edges.jsonl`;
- `ig_patch_spectral_signatures.jsonl`;
- `manifest.json`.

The manifest includes:

- `run_id`;
- schema versions;
- input file hashes;
- output file hashes;
- generator version.

### Stage B: Validate

Checks:

- schema validity;
- `patch_id` and `run_id` consistency;
- referential consistency among patch artifacts;
- claim-policy fields.

### Stage C: Ingest

Requirements:

- deterministic duplicate handling;
- collection/index registry use;
- import report JSON;
- no mutation of formal Lean source facts.

### Stage D: Verify

AQL invariants:

- counts match manifest;
- every member references an existing patch in the same run;
- every spectral row references an existing patch in the same run;
- every patch edge references source and target patches in the same run;
- run-level summary is internally consistent.

### Stage E: Report

Reports include:

- machine-readable JSON;
- human summary;
- selected `run_id`;
- compatibility-path flags;
- schema versions;
- pass/fail semantics.

## 7. Safety And Claim Governance

Machine-enforced policy fields:

- `claim_scope`;
- `non_overclaim`;
- `authority_level`;
- `proof_link` when `authority_level` is formal-adjacent.

Accepted authority levels:

- `heuristic`;
- `derived`;
- `formal`.

CI rejects:

- missing policy fields;
- formal authority escalation without a proof link;
- lane-mixing violations;
- sidecar artifacts presented as proof objects.

## 8. Testing Strategy

Unit tests:

- schema validators;
- environment alias normalization;
- versioned adapters;
- run-id resolver logic.

Contract tests:

- query input shape;
- query output shape;
- CLI JSON output shape;
- schema version compatibility.

Integration tests:

- local Arango with auth enabled;
- ingest and verify cycle;
- mixed historical dataset compatibility.

Regression tests:

- legacy run-key style fixture;
- modern `run_id` style fixture;
- mixed coexistence fixture.

## 9. Migration Plan From Current Repo

Phase 1: non-breaking shell.

- Keep existing scripts.
- Introduce `src/igf` library modules.
- Make wrappers call the new library internally.

Phase 2: contract hardening.

- Add schema files and validators.
- Add manifest generation.
- Add contract tests in CI.

Phase 3: query unification.

- Move ad hoc AQL into the query registry.
- Replace prefix-based verification with `run_id` joins.

Phase 4: deprecation.

- Mark old scripts deprecated.
- Remove duplicate auth and environment code paths.
- Enforce `igf` CLI in CI workflows.

## 10. First Two-Week Implementation Slice

Week 1:

1. Create or normalize repo skeleton and CLI scaffold.
2. Implement typed config, env alias normalization, and preflight.
3. Add schemas and validator.
4. Implement deterministic manifest writing.

Week 2:

1. Implement ingest module with collection/index registry.
2. Implement verify module with canonical `run_id` semantics.
3. Add integration tests against auth-on Arango.
4. Wire CI gates for schema, integration, and regression fixtures.

End-of-slice deliverable:

- `igf run` works locally end to end;
- latest summary works under mixed legacy data;
- no string-prefix counting dependency remains.

## 11. Definition Of Done

Greenfield done means all are true:

- one canonical `run_id` model;
- all artifact and ingest boundaries are schema validated;
- one CLI orchestrator runs the full pipeline;
- auth-on integration passes;
- mixed legacy compatibility is tested;
- no-overclaim policy is enforced in CI;
- manifests are deterministic;
- runs are reproducible from source artifacts.
