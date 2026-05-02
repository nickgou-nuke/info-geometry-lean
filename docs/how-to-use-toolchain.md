# How to Use the DAG Toolchain

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

## Overview

This document describes the complete DAG toolchain, the expected execution order, and the purpose, inputs, and outputs of each infrastructure script.

## Pipeline Order

1. Indexer
2. `tools/infra/run_full_dag_toolchain.py`
3. `tools/infra/materialize_lossless_infotree.py`
4. `tools/infra/hydrate_arango_topology.py`
5. `tools/infra/arango_layered_ingest.py`
6. `tools/infra/arango_dag_algorithms.py`
7. `tools/infra/arango_structural_vacuity_audit.py`

## Resiliency Behavior

Some pipeline stages are data-dependent. In a clean run, Lean may export no anomalies. In that case, `artifacts/dag/process-flow/` may not exist.

The following scripts support `--allow-missing-input`:

- `generate_process_flow_report.py`
- `generate_semantic_flow_report.py`
- `check_semantic_flow_report.py`

When the flag is present, missing or empty optional inputs produce structurally valid clean reports and exit with status code `0`.

Malformed non-empty inputs still fail.

## Script Reference

### `run_full_dag_toolchain.py`

Purpose: Orchestrates the DAG analysis pipeline.

Inputs:

- Lean/exported DAG artifacts
- Existing `artifacts/dag/` tree
- Optional process-flow artifacts

Outputs:

- Derived DAG reports
- Process-flow reports
- Semantic-flow reports
- Validation/check results

Notes:

- Passes `--allow-missing-input` to optional downstream flow-report stages.

### `generate_process_flow_report.py`

Purpose: Generates a process-flow report from process event and flow edge JSONL files.

Inputs:

- `flow-edges.jsonl`
- `process-events.jsonl`

Outputs:

- Process-flow JSON report
- Process-flow Markdown report

Empty-input behavior:

- With `--allow-missing-input`, writes a clean empty report and exits `0`.
- Without the flag, missing or empty inputs fail.

### `generate_semantic_flow_report.py`

Purpose: Generates semantic-flow analysis from upstream DAG/process-flow artifacts.

Inputs:

- Semantic-flow source artifacts
- Process-flow report artifacts, depending on current implementation

Outputs:

- Semantic-flow JSON report
- Semantic-flow Markdown report

Empty-input behavior:

- With `--allow-missing-input`, writes a clean empty report and exits `0`.
- Without the flag, missing inputs fail.

### `check_semantic_flow_report.py`

Purpose: Validates semantic-flow report results and fails CI/toolchain execution when findings exceed allowed thresholds.

Inputs:

- Semantic-flow JSON report

Outputs:

- Exit status
- Console diagnostics

Empty-input behavior:

- With `--allow-missing-input`, missing or empty reports are treated as clean.
- Existing reports with actual failures still fail.

### `materialize_lossless_infotree.py`

Purpose: Materializes a lossless infotree representation from indexed artifacts.

Inputs:

- Indexed DAG/source artifacts

Outputs:

- Lossless infotree artifact tree

### `hydrate_arango_topology.py`

Purpose: Converts materialized DAG/infotree artifacts into topology structures suitable for ArangoDB ingestion.

Inputs:

- Materialized DAG/infotree artifacts

Outputs:

- ArangoDB topology documents and edge definitions

### `arango_layered_ingest.py`

Purpose: Ingests layered DAG/topology artifacts into ArangoDB.

Inputs:

- Hydrated Arango topology artifacts
- ArangoDB connection configuration

Outputs:

- Populated ArangoDB vertex and edge collections

### `arango_dag_algorithms.py`

Purpose: Runs graph algorithms against the ingested ArangoDB DAG topology.

Inputs:

- ArangoDB collections
- DAG topology graph

Outputs:

- Algorithmic analysis artifacts
- Console/report output

### `arango_structural_vacuity_audit.py`

Purpose: Audits the ArangoDB DAG to find structurally vacuous or admitted local theorems using strict graph topologies (identifying bypasses, sorryAx dependencies, or missing foundational connections).

Inputs:

- ArangoDB collections (`ig_nodes`, `ig_edges`)

Outputs:

- Structural Vacuity JSON audit report
- Structural Vacuity Markdown audit report
- Optional exit status `1` if findings are present (`--fail-on-findings`)
