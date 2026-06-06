# Lean Sandbox for Pi Extension

This directory is a placeholder for a future standalone Lean project
with mathlib support.

Currently, the `verify_lean_proof` tool uses:
- **Plain mode**: `lean <file>` directly (for code without `import Mathlib`)
- **Mathlib mode**: the existing `info-geometry-lean` project at
  `/home/goutev/info-geometry-lean/` which has mathlib v4.28.0 pre-built

To set up this directory as a standalone sandbox in the future:
```bash
cd lean_sandbox
lake update
lake build
```
