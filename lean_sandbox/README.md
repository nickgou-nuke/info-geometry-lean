<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](docs/REPO_DEEP_SEARCH_PROTOCOL.md).

# Lean Sandbox for Pi Extension

This directory is a placeholder for a future standalone Lean project
with mathlib support.

Currently, the `verify_lean_proof` tool uses:
- **Plain mode**: `lean <file>` directly (for code without `import Mathlib`)
- **Mathlib mode**: the existing `info-geometry-lean` project which has mathlib pre-built

To set up this directory as a standalone sandbox in the future:
```bash
cd lean_sandbox
lake update
lake build
```
