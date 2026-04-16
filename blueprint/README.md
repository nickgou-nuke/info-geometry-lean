# Blueprint Workflow

This directory documents the LeanArchitect-facing blueprint layer.

## Current source of blueprint coverage

Blueprint tags are generated from the declaration graph into:
- `lean/InfoGeometry/auto_blueprints.lean`
- `lean/InfoGeometry/BlueprintTags.lean`

Refresh path:

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprintJson
```

## Checked-in blueprint files

The checked-in `blueprint/` directory contains only the human-facing wrapper files that live beside LeanArchitect output, such as `print/print.tex` and `print/blueprint.sty`.

The exhaustive generated blueprint payload is emitted under `.lake/build/blueprint/`.

## Rule

- Treat `blueprint/` as the human-facing wrapper layer.
- Treat `auto_blueprints.lean` and `BlueprintTags.lean` as generated/refreshable.
- Do not confuse exhaustive node extraction with a curated mathematical monograph.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md) for the current build/audit state.

