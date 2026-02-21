# InfoGeometry Architecture

This document describes the dependency DAG, module boundaries, and design principles for the InfoGeometry Lean 4 library.

## Layer Order

- Finite Probability
- KL (finite)
- Partition / Φ
- Bregman
- Exponential Families
- Grand Canonical
- Jordan / SPD
- Architecture

No upward imports. See Lean files for mathematical content.

## Public Surfaces

- Canonical/stable: `lean/InfoGeometry.lean` (imports `InfoGeometry/Library.lean`)
- Experimental/non-canonical: `lean/InfoGeometry/Experimental.lean`
- Canonical domains: `lean/InfoGeometry/Canonical/{Foundations,Statistics,Algebra,Geometry,All}.lean`
- Legacy wrappers: `lean/InfoGeometry/{Clifford,Krein,Projective,Prequantum,Quantum,Twistor}.lean`

Publishing and downstream projects should import the canonical root.
CI/strict-check enforce that canonical modules do not import `InfoGeometry.Experimental`.
