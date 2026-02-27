# Top-level scripts

This directory contains general-purpose tooling for the InfoGeometry project.
The emphasis is on documentation, metadata extraction, and cross-package
analysis.  It is **not** tied to the Lean build system; all scripts are
Python (or Lean) and can be invoked from the repository root.

## Sub‑areas

- `build_doc_map.py`, `emit_markdown_index.py`, `filter_project_decls.py`,
  `auto_tag.py`, `gen_content_auto_tex*.py` – work with the `docs-map`
  directory and generate files used in the manual or by the blueprint
  package.
- `namespace_patch_plan.py` and `audit_namespaces.sh` – assist with
  namespace hygiene.
- `ci_baseline.sh` – runs the canonical green baseline used by CI:
  `lake build`, `make-graph --probe-unresolved`, `refactor-plan`,
  and archive-policy enforcement.
- `ExportDecls.lean` and `emit_blueprint_tex.py` – export data from a
  `Lean.Environment` for analysis.
- `ExportGraph.lean` + `make_graph.py` – produce a dependency graph (nodes +
  edges) from the current environment and write it as JSON.  The exporter now
  records the kind of each edge (`type` vs `value`) and `make_graph.py` will
  summarise the kinds; existing consumers can still handle the older pair-based
  format.
- A shared Python library, `tools/`, holds common utilities (see
  `tools/pathing.py`).

## Usage

Run individual scripts either directly (they contain a shebang) or via
``python -m`` to ensure the `tools` package is importable.  In future the
scripts directory will have a unified CLI, so you can dispatch subcommands
from a single entry point:

```sh
python -m scripts build-doc-map --help
python -m scripts auto-tag --path docs-map/declarations.json
# or continue to invoke the individual modules while the CLI is in beta
python -m scripts.build_doc_map --help
```

Additional documentation and the intent of each script is included at the
head of the file itself.
