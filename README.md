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
- Python 3 for optional visualization scripts (`numpy`, `matplotlib`)

## Structure

- `lean/` - Lean source code and configuration
	- `InfoGeometry.lean` - canonical published entrypoint (stable surface)
	- `InfoGeometry/Library.lean` - stable linted umbrella imported by `InfoGeometry.lean`
	- `InfoGeometry/Canonical/` - canonical domain umbrellas (`Foundations`, `Statistics`, `Algebra`, `Geometry`, `All`)
	- `InfoGeometry/Experimental.lean` - exploratory/compatibility umbrella (non-canonical)
	- `InfoGeometry/{Clifford,Krein,Projective,Prequantum,Quantum,Twistor}.lean` - legacy compatibility wrappers
	- `all_lean_files_combined.lean` - archive-only concatenation for LLM context (non-canonical; excluded from CI/strict checks)
	- `InfoGeometry/` - information-geometry modules (`KL`, `Fenchel`, `Renyi`, `Cramer`)
	- `Clifford/`, `Projective/`, `Prequantum/`, `Krein/` - domain scaffolds
- `notes/` - Documentation and development notes
- `.github/workflows/` - CI/CD configuration

## Catastrophe Surface Visualization

To render the three-stage free-energy catastrophe surface:

```bash
python3 lean/scripts/catastrophe_surface.py --save docs/catastrophe_surface.png
```

Optional interactive view:

```bash
python3 lean/scripts/catastrophe_surface.py --show --save /tmp/catastrophe_surface.png
```
