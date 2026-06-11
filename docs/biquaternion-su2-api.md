# Biquaternion SU(2) API

> Status: finite shadow owner surface
> Owner: `lean/InfoGeometry/Canonical/BiquaternionSU2.lean`

This module packages the biquaternion commutator witness for the `SU(2)`-style
generator relations.

## Proved Statements

- `biquaternion_su2_ij`
- `biquaternion_su2_jk`
- `biquaternion_su2_ki`

## Proof Boundary

- The file proves the commutator identities for the named generators.
- It does not prove a full Lie-algebra classification theorem.
- It does not identify the biquaternion lane with a continuum weak-force model.

## Use Case

- Use this module as the canonical owner for the finite `SU(2)` commutator shadow.
- Use [ModuleMap.md](ModuleMap.md) to navigate from the canonical surface to the owner file.
