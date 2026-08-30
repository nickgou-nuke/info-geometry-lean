# Debt Protocol

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this workflow, but subordinate to repo-wide authority docs and code.
> See: [README.md](README.md), [docs/README.md](docs/README.md), [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md)

Debt work here means replacing stale, wrapper-heavy, duplicated, or surrogate
surfaces with cleaner owner mathematics.

## Current Debt Signals

Treat these as real debt:

- wrappers that add no new mathematics
- duplicated presentation layers over one lower trunk
- stale umbrella ownership
- surrogate theorem surfaces that should collapse into lower owners

Do not call something debt merely because it is abstract, small, or not yet
connected to a larger story.

## Current Debt Method

1. Read the owner file directly.
2. Find direct consumers.
3. Remove or shrink one debt surface at a time.
4. Rebuild the affected file/module.
5. Use report surfaces only as second-pass confirmation.

## Useful Commands

```bash
lake env lean <changed-file>.lean
lake script run changedVerify
lake script run dagDoctor
```

Secondary analysis tools:

- `tools/infra/generate_theorem_surface_index.py`
- `tools/infra/generate_semantic_quotient.py`
- `tools/infra/generate_projection_coloring.py`

## Rule

Debt reduction should make the code smaller, clearer, or more owner-faithful.
If the patch mostly renames, rearranges, or rebrands, it probably is not paying
debt.
