# Quaternion Embedding API

> Status: finite matrix witness owner surface
> Owner: `lean/InfoGeometry/Canonical/QuaternionEmbedding.lean`

This module packages a concrete Dirac-matrix witness for the quaternion
generator relations used by the finite quaternion condensate lane.

## Proved Statements

- `embedI_sq`
- `embedJ_sq`
- `embedK_sq`
- `embedI_mul_embedJ`
- `embedJ_mul_embedK`
- `embedK_mul_embedI`
- `embedJ_mul_embedI`
- `embedK_mul_embedJ`
- `embedI_mul_embedK`
- `embedI_mul_embedJ_mul_embedK`
- `embedH4_one`
- `embedH4_i`
- `embedH4_j`
- `embedH4_k`

## Proof Boundary

- The file proves a finite matrix witness in the selected Dirac-Pauli model.
- It does not prove a universal algebra equivalence `ℍ ≃ Cl(0,2)`.
- It does not prove a full embedding theorem for `Cl(1,3; ℂ)`.

## Use Case

- Use this module as the canonical matrix witness for the quaternion basis
  inside the Clifford bridge lane.
- Use [ModuleMap.md](ModuleMap.md) to navigate from the canonical surface to the owner file.
