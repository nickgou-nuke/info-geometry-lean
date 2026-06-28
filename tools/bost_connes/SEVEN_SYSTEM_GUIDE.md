# Bost-Connes seven-system guide — corrected status

## Purpose

This file is a conservative guide to what the repository currently has.
It is not a claim of complete seven-system closure.

## What is currently real

### Executed local script
- `tools/bost_connes/sympy_liouville_modular.py`
- executable and run successfully in this repo session

### Build-verified Lean packets
- `tools/bost_connes/lean/InfoGeometry/Canonical/EntropyCorrection_Boltzmann_vs_vonNeumann.lean`
- `lean/InfoGeometry/OperatorAlgebra/CliffordInfinityCommutation.lean`

These are real verified artifacts, but they are not by themselves a complete
seven-system Bost-Connes theorem package.

## How to interpret the other system files

SageMath, GAP, Macaulay2, Coq, and Isabelle files may exist as companions,
sketches, or execution targets. This guide does not treat their presence alone
as audited verification of the same narrowed statement.

## What would be required for a real seven-system guide

For each system, we would need:
1. the exact same narrowed statement;
2. a checked artifact in that system;
3. explicit verification output;
4. theorem-honest documentation of scope and limitations.

That standard is not yet met globally.

## Bottom line

Use this lane as a repository of partial cross-system work plus a few verified
local owner artifacts, not as completed seven-system closure.
