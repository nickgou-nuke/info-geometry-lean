# Installation and First Build

This repository uses:
- Lean toolchain: `leanprover/lean4:v4.28.0`
- Lake package management via [lakefile.lean](lakefile.lean)
- optional repo-local Python environment under `.venv`

## Prerequisites

Install:
- `git`
- `python3`
- `pip`
- `elan` with Lean 4 support

## Clone and bootstrap

```bash
git clone <your-remote> info-geometry-lean
cd info-geometry-lean
```

Optional but recommended for mathlib cache:

```bash
lake exe cache get
```

## Python environment

The repo does not require a large Python dependency stack for basic builds, but the tooling is easier to use from a local virtual environment.

```bash
python3 -m venv .venv
. .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e .
```

If you use the local skill validator or other YAML-aware tooling, also install:

```bash
python -m pip install PyYAML
```

## First Lean builds

Small smoke build:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.Canonical.All
```

Full umbrella build:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.All
```

Repo quality gate:

```bash
lake script run strictCheck
```

## First graph refresh

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/generate_theorem_surface_index.py
python3 tools/infra/generate_source_sink_compression.py
```

Continue with the rest of the maintained sequence from [README.md](README.md) or [tools/infra/README.md](tools/infra/README.md).

## Optional: Runtime Thermo Conformance Audit

If you capture open-weights runtime traces (JSONL), you can audit them against
the finite theorem lane (`KMSSoftmaxBridge`, `RouterFreeEnergyBridge`,
`PromptDefectRegularization`):

```bash
python3 tools/infra/llm_thermo_conformance.py \
  --input traces/runtime_router.jsonl \
  --json-out reports/llm/thermo_conformance.json \
  --md-out reports/llm/thermo_conformance.md \
  --strict-schema \
  --fail-on-violation
```

Input schema:
- `tools/schema/llm_thermo_trace.schema.json`

## Notes

- Use the locked build wrapper for umbrella builds; do not run concurrent `lake build` jobs.
- Treat `reports/` and `docs/auto/` as generated outputs, not as setup instructions.
- If a document disagrees with the code, trust the code and the maintained scripts.
