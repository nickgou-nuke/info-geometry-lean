# Quaternion Cartan Decomposition API

> Status: finite matrix witness owner surface
> Owner: `lean/InfoGeometry/Canonical/CartanInvolution.lean`

This module packages a concrete Dirac-matrix witness for the quaternion
generator relations used by the finite quaternion condensate lane.
The intended interpretation is Cartan-decomposition-by-involution, not a
literal universal embedding theorem.

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
- It does not prove a full Cartan decomposition theorem for `Cl(1,3; ℂ)`.
- It does not formalize the Möbius gluing of `det = 0` and `1/det = 0`.

## Use Case

- Use this module as the canonical matrix witness for the quaternion basis
  inside the Cartan/involution bridge lane.
- Use [ModuleMap.md](ModuleMap.md) to navigate from the canonical surface to the owner file.
