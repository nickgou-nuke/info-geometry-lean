# Bost-Connes thermofield dynamics — corrected status

## Overview

This directory contains exploratory and partially verified work around a
Bost-Connes commutation lane.

A narrow checked statement in the nearby computational lane is that the script
`tools/bost_connes/sympy_liouville_modular.py` successfully executes its bounded
arithmetic/scalar commutation checks.

## Verified artifacts in the current audit

### SymPy
- Run with:
  `python3 tools/bost_connes/sympy_liouville_modular.py`
- Status: executed successfully in this repo session

### Lean entropy correction packet
- File: `tools/bost_connes/lean/InfoGeometry/Canonical/EntropyCorrection_Boltzmann_vs_vonNeumann.lean`
- Status: verified with `lake env lean`

### Lean Clifford colimit commutation lane
- File: `lean/InfoGeometry/OperatorAlgebra/CliffordInfinityCommutation.lean`
- Status: verified with `lake build InfoGeometry.OperatorAlgebra.CliffordInfinityCommutation`

## How to read the rest of this directory

Other scripts and proof files may be useful companions, but their presence alone
should not be read as completed verification of a shared theorem package.

## Open debt

Still needed:
- an exact owner theorem for the Bost-Connes narrative layer
- audited builds or runs for the companion systems
- exact downstream consequences stated and checked in owner files
- continued cleanup of narrative overreach in adjacent docs

## Bottom line

This directory contains a mix of exploratory materials and a few verified local
artifacts. The broader synthesis remains unfinished.
