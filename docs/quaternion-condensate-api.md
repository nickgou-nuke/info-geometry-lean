# Quaternion Condensate API

> Status: `finite shadow`
> Owner: `lean/InfoGeometry/Canonical/QuaternionCondensate.lean`
> Companion witness: `tools/sympy/quaternion_condensate.py`

This page records the source-owned quaternion condensate packet.

## What is proved

- quaternion basis laws for the finite `H4` carrier
- conjugation and norm identities
- unit-phase norm preservation in the `1-i` plane
- commutator antisymmetry
- torsion-readout antisymmetry from an antisymmetric commutator input

## What is not proved

- `ℍ ≃ Cl(0,2)` as a formal Lean equivalence
- a Cartan/involution realization theorem inside `Cl(1,3; ℂ)`
- a continuum electromagnetic gauge-field theorem
- a continuum Einstein-Cartan derivation

## Practical use

Use this module as the finite quaternion condensate shadow for the emergent
geometry lane. It is the source-owned endpoint for coefficient algebra, not a
replacement for the Cartan/involution witness or octonionic continuation work.
