# Tooling Overview

The supported Python-side tooling is split into three maintained surfaces:
- [tools/infra/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/infra/README.md)
- [tools/frontier/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/frontier/README.md)
- [tools/docs/README.md](/home/goutev/LEAN4/info-geometry-lean/tools/docs/README.md)

Top-level `tools/*.py` files exist mainly as compatibility wrappers or convenience entrypoints. The maintained workflow should be read from the three subdirectory READMEs above.

## Current split

### `tools/infra`
Maintained graph refresh, DAG reports, theorem-surface classification, semantic quotient, projection coloring, and build locking.

### `tools/frontier`
Maintained semantic-block export and frontier exploration for heavy modules.

### `tools/docs`
Maintained doc refresh helpers for generated documentation surfaces.

## Current rule

If documentation about the tooling disagrees, trust:
1. the scripts under `tools/infra/`, `tools/frontier/`, and `tools/docs`;
2. then the corresponding READMEs;
3. only then any older top-level wrapper doc.
