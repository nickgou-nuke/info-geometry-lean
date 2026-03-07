# Witten Synthesis

This note summarizes the spectral-topological bridge around Witten-Laplacian
and Seeley-DeWitt structures in the canonical stack.

## Chain Overview

1. Supersymmetric inference:
   supercharge operators pair natural and expectation coordinates.
2. Witten Laplacian:
   the supersymmetric Hamiltonian `H = {Q, Q†}` controls topological zero modes.
3. Heat-kernel expansion:
   spectral traces of `exp(-t D^2)` expose geometric invariants.
4. Seeley-DeWitt coefficients:
   `a0` tracks spectral volume; `a1` tracks scalar-curvature content.
5. Einstein-Hilbert bridge:
   curvature action terms are extracted from low-order heat coefficients.

## Canonical Route In Code

1. `Canonical/SuperInference.lean`:
   supercharge/super-Hamiltonian interfaces (Witten-Laplacian interpretation).
2. `Canonical/HeatKernel.lean`:
   heat trace model and Seeley-DeWitt coefficient interfaces.
3. `Canonical/AnalyticalIndex.lean`:
   spectral-index side conditions linking zero modes to topological invariants.

## Canonical Entry Points

- `InfoGeometry.Canonical.SuperInference`
- `InfoGeometry.Canonical.HeatKernel`
- `InfoGeometry.Canonical.AnalyticalIndex`
