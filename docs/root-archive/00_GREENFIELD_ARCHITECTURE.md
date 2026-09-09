# Greenfield Architecture Note

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Future-state architecture sketch. Not part of the maintained authority surface.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

This file captures a future-facing architecture direction for the repository.

## Current Role

Treat it as a design sketch for possible consolidation of pipeline commands and
run identity, not as a description of the current live system.

## Current System Instead

The live system today is centered on:

- `lean/`
- `src/igf/`
- `tools/`
- `lakefile.lean`

For current operator surfaces, use:

- [README.md](README.md)
- [docs/ToolingMethodology.md](docs/ToolingMethodology.md)
- [docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md](docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md)
