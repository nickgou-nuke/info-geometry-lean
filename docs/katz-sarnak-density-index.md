# Katz-Sarnak Density Index

> Status: `current authority`
> Audited: 2026-06-11
> Scope: finite and conditional symmetry readouts only
> Boundary: this index summarizes the repo surfaces that mirror bulk GUE and
> critical-line symmetry behavior.  It does not claim a proven Katz-Sarnak
> density theorem, an `n`-level density theorem, or a family-level random
> matrix universality theorem.

This document is the compact owner map for the Katz-Sarnak style symmetry lane
already present in the repository.

## 1. Bulk GUE lane

Owner files:

- [lean/InfoGeometry/Canonical/PrimonGasGUE.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/PrimonGasGUE.lean)
- [tools/sympy/gue_pair_correlation.py](/home/goutev/repos/info-geometry-lean/tools/sympy/gue_pair_correlation.py)
- [tools/sympy/cantor_cuntz_background_potential.py](/home/goutev/repos/info-geometry-lean/tools/sympy/cantor_cuntz_background_potential.py)

Finite theorem-backed fact:

- `trap_is_conserved_charge` proves that the trap projector commutes with the
  Hamiltonian under the explicit invariance hypothesis.

Repo meaning:

- this is the finite bulk GUE shadow: a conserved trap splits the spectrum,
  but the file does not prove any universal pair-correlation theorem.

## 2. Critical-line / antiunitary lane

Owner files:

- [lean/InfoGeometry/Arithmetic/ZetaSouriauComplexLift.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/ZetaSouriauComplexLift.lean)
- [tools/sympy/completed_xi_projector_bridge.py](/home/goutev/repos/info-geometry-lean/tools/sympy/completed_xi_projector_bridge.py)
- [lean/InfoGeometry/Arithmetic/PrimonChiralSouriauThermodynamics.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/PrimonChiralSouriauThermodynamics.lean)

Finite theorem-backed facts:

- the antiunitary reflection is an involution;
- the fixed locus is the critical line;
- the normalized finite fermionic density sums to one when the partition is nonzero.

Repo meaning:

- this is the finite antiunitary/critical-line shadow that often gets read as a
  symmetry-locus analogue of the low-lying zero story.

## 3. Family-density / zeta-lift lane

Owner files:

- [lean/InfoGeometry/Arithmetic/PrimeDistributionLaw.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/PrimeDistributionLaw.lean)
- [lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalMassieuBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalMassieuBridge.lean)
- [lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean)

Finite theorem-backed facts:

- finite density readouts and prime cutoff formulas are owned here;
- the Majorana/Pólya-Hilbert lane is explicitly a socket, not a proved RH
  theorem;
- analytic continuation and spectral-determinant claims remain open.

## 4. Summary

The repo already has the pieces that one would use to build a Katz-Sarnak
style story:

- finite bulk GUE trap conservation;
- critical-line antiunitary reflection;
- finite density readouts on prime/zeta towers;
- explicit analytic sockets for the missing spectral claims.

What it does **not** yet have is a theorem-level n-level density or a family
random-matrix universality statement.
