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
	- `InfoGeometry.lean` - current monolithic development (compatibility root)
	- `InfoGeometry/Library.lean` - modular import hub
	- `InfoGeometry/` - information-geometry modules (`KL`, `Fenchel`, `Renyi`, `Cramer`)
	- `Clifford/`, `Projective/`, `Prequantum/`, `Krein/` - domain scaffolds
- `notes/` - Documentation and development notes
- `.github/workflows/` - CI/CD configuration