# DAG Troubleshooting

> Status: `maintained local guide`
> Audited: 2026-05-14 against current scripts.
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Use this page when the managed DAG lane is stale, blocked, or inconsistent.

## Build Lock Is Held

Check status first:

```bash
lake script run dagStatus
```

If another active build is running, wait for it to finish and then rerun:

```bash
lake script run dagAll
```

If the lock metadata is stale but no real build is active, clear it using the repo's normal locked-build cleanup path rather than deleting files manually.

## Authoritative Artifacts Are Missing Or Stale

Run:

```bash
lake script run dagRefresh
```

Then regenerate reports and re-diagnose:

```bash
lake script run dagReports
lake script run dagDoctor
```

Or do the full managed repair:

```bash
lake script run dagAll
```

## Deleted/Renamed Lean Files Still Appear In DAG Reports

Symptom:
- declarations from removed or renamed files keep appearing in `reports/dag/*`
- refresh runs look "green" but downstream reports still reference old paths

Cause:
- this was usually an incremental-skip mismatch: index refresh skipped because build hashes looked unchanged, while stale `decls.jsonl` rows still pointed at now-missing source files.

Current behavior:
- `refresh_decl_graph.py` now checks for missing source paths in `artifacts/dag/index/decls.jsonl` before honoring a skip.
- if stale paths are found, it forces a refresh automatically.
- `dagDoctor` now reports `source hash` freshness and fails on unresolved decl source paths.

Manual recovery order (if you still suspect contamination):

```bash
lake script run dagStatus
lake script run dagRefresh -- --force
lake script run dagReports
lake script run dagDoctor
```

## Reports Are Missing Or Stale

Run:

```bash
lake script run dagReports
```

Then confirm:

```bash
lake script run dagDoctor
```

## The Indexer Or Managed Refresh Failed

First get the exact diagnosis:

```bash
lake script run dagDoctor
```

Common causes:
- build target does not compile
- stale or partial artifacts
- local environment drift
- interrupted report generation

If the underlying Lean build is the issue, fix the build first and rerun:

```bash
lake script run dagAll
```

If the failure is a prebuild failure for `InfoGeometry.All`, no fresh native DAG
was generated. Do not run Arango overlay analysis as if it describes current
source. Use source-level audits until the build blocker is fixed.

Common prebuild symptoms:

- Lean module typeclass failures.
- syntax errors in newly imported files.
- unresolved identifiers from half-installed bridge modules.
- `InfoGeometry.All` imports a broken experimental module.

## Coverage Policy Failed (Partial Graph)

If `generate_causal_report.py` or `dagDoctor` fails on coverage policy, check
the current gap first:

```bash
python3 tools/infra/dag_status.py
python3 tools/infra/dag_doctor.py
```

If you need a diagnostic report while coverage is still partial, run:

```bash
python3 tools/infra/generate_causal_report.py --out reports/dag/true-root-order.md --json-out reports/dag/true-root-order.json --allow-partial-coverage
```

Use this only as an explicit diagnostic mode. Do not treat it as strict green health.

## I Need To Find Open Sockets While The DAG Is Blocked

Run the source closure-debt scanner:

```bash
python3 tools/quality/closure_debt_crawler.py \
  --root lean/InfoGeometry \
  --json-out reports/audit/closure-debt-crawler.json \
  --md-out reports/audit/closure-debt-crawler.md \
  --print-summary
```

This does not depend on a fresh DAG. It finds source-level debt patterns such as
`Prop := True`, `sorry`, `admit`, `axiom`, skeletal one-line proofs, witness
packets, and bridge/socket naming surfaces.

It is not a graph crawler. It does not answer source-sink chain or Mathlib
reachability questions.

Use `--strict` only when you want hard findings to return nonzero.

## I Need Source-Sink Chains Or Mathlib Reachability

Use native DAG reports first:

```bash
lake script run dagRefresh
lake script run dagReports
lake script run dagDoctor
```

The relevant local reports are produced by:

- `tools/infra/generate_source_sink_compression.py`
- `tools/infra/generate_causal_report.py`
- `tools/theorem_significance.py`

If `dagRefresh` fails, these reports are stale or unavailable for current
source. Fix the build or run only source-level audits.

Run Arango only after native DAG refresh and ingest/descent verification.

## Blueprint Or Depth Tags Look Wrong

Refresh the tag surfaces first, then rerun the managed lane if needed.

Typical repair commands:

```bash
python3 tools/infra/refresh_blueprint_tags.py
lake script run dagAll
```

## Process-Flow Report Takes Too Long

Run the process-flow lane in two steps and keep the Lean export as the authoritative artifact boundary:

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

If the Python report step is too heavy for the current machine state, keep the exported JSONL process-flow artifacts and defer report regeneration until the machine is less loaded.

## I Only Changed Lean Files

Do not run the whole DAG lane by default. Start with:

```bash
lake script run changedVerify
```

Add `--dry-run` if you only want the planned commands:

```bash
lake script run changedVerify -- --dry-run
```

## I Need Local Proof-State Or Frontier Work

Use the proof/frontier tools, not DAG refresh:

```bash
lake script run proofSession
lake script run proofPrint -- InfoGeometry.Canonical.SomeModule
lake script run semanticSnapshot
```

## Repair Order

Use this order unless you have a specific reason not to:

1. `lake script run dagDoctor`
2. `lake script run dagAll`
3. `lake script run changedVerify` for changed Lean work

For current-source graph work, the hard gate is:

```text
InfoGeometry.All builds
dagRefresh succeeds
dagDoctor does not report stale source/olean hashes
```
