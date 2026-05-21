# NormalOrderedCurrent

`InfoGeometry.Canonical.NormalOrderedCurrent` is now restricted to the clean
finite theorem that the repo can prove from canonical mathlib matrix units.

Implemented in Lean:

- `matrixUnit`: the canonical `Matrix.single a b 1`.
- `matrixUnit_commutator`: the ordinary matrix-unit commutator.
- `normalOrderedMatrixUnit`: subtracts an occupied diagonal scalar multiple of
  the identity.
- `normalOrdered_matrixUnit_commutator`: the finite Wick correction obtained by
  rewriting the matrix-unit commutator in the normal-ordered basis.

This file intentionally does not define raw CAR mode records, assumed current
laws, theorem sockets, or a completed Heisenberg current theorem.

The completed raw-CAR-to-current theorem is still not present. It requires a
genuine mode-indexed Fock/CAR construction and a completed normal-ordered
current sum. The finite matrix-unit theorem is the canonical algebraic piece
that exists now.
