# info-geometry-lean

This repository contains Lean 4 formalizations for information geometry, exploring the geometric structures of statistical manifolds and their applications.

## Build Instructions

To build the project:

```bash
cd lean
lake update
lake build
```

## Requirements

- Lean 4 (version specified in `lean/lean-toolchain`)
- Lake (Lean's build tool, included with Lean)

## Structure

- `lean/` - Lean source code and configuration
- `notes/` - Documentation and development notes
- `.github/workflows/` - CI/CD configuration