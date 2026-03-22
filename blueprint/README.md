# Blueprint Workflow

This directory is the human-facing blueprint layer.

There are two distinct parts:

1. Lean declaration selection and exact node extraction
- tags live in `lean/InfoGeometry/auto_blueprints.lean`
- façade module is `lean/InfoGeometry/BlueprintTags.lean`
- tags are refreshed from the public declaration graph with:

```bash
python3 tools/infra/refresh_decl_graph.py
python3 tools/infra/refresh_blueprint_tags.py
```

2. LeanArchitect emission
- exact TeX / JSON node extraction is handled by LeanArchitect facets
- the dedicated module build is:

```bash
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprint
python3 tools/infra/run_locked_lake_build.py InfoGeometry.BlueprintTags:blueprintJson
```

This writes LeanArchitect artifacts under `.lake/build/blueprint/`.

Single-build rule:
- do not start concurrent full or umbrella builds from multiple terminals or MCP sessions
- use `python3 tools/infra/run_locked_lake_build.py ...` so a second build fails fast instead of stuttering the workspace

## Human-readable document

Do not confuse exhaustive node coverage with readable mathematical exposition.

- exact node renderings belong to LeanArchitect outputs and `\inputleannode{...}` stubs
- human-readable theory narrative belongs in `blueprint/src/generated/content.tex`
- printable assembly happens through `blueprint/print/print.tex`

Current default scaffold:
- `blueprint/src/generated/content.tex` includes the generated library index
- that is exhaustive, but not yet a real mathematical monograph

The right long-term structure is:
- curated chapters in `content.tex`
- selective `\inputleannode{...}` inclusions for exact formal statements
- generated index material appended as reference, not used as the whole narrative

## Legacy scripts

These older bootstrap scripts are not the authoritative workflow anymore:
- `archive/legacy/scripts/graph_to_blueprint_inplace.py`
- `archive/legacy/scripts/graph_to_blueprint_bulk.py`
- `archive/legacy/scripts/auto_tag.py`
- `archive/legacy/scripts/generate_library_index.py`
- `archive/legacy/scripts/agent_doc_gen.py`

They are still useful for archaeology or one-off conversions, but the supported path is:
- `artifacts/dag/` for declaration coverage
- `tools/infra/refresh_blueprint_tags.py` for blueprint tag refresh
- LeanArchitect facets for exact TeX/JSON extraction
