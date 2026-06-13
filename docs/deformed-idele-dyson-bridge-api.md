# Deformed Idele Dyson Bridge API

Lean owner: `lean/InfoGeometry/Canonical/DeformedIdeleDysonBridge.lean`

This module is a narrow finite bridge from branch nonunitarity to scalar
Vandermonde/Dyson exclusion geometry.

## Core Packet

`BranchDefectToDysonNodes` carries:

- `branch : A`
- `branch_isometry : star branch * branch = 1`
- `nodes : Fin N -> Real`
- `range_defect_forces_injective_nodes`

The final field is the explicit missing bridge theorem: it says a range
projection defect forces the scalar node readout to be injective.

## Verified Readouts

| Theorem | Content |
|---|---|
| `branch_commutator_ne_zero` | range defect makes the branch commutator nonzero |
| `nodes_injective_of_range_defect` | range defect gives injective scalar nodes via the supplied bridge premise |
| `nodes_noncollision_of_range_defect` | injective scalar nodes cannot collide on ordered pairs |
| `dyson_to_vandermonde_of_range_defect` | finite Dyson Hamiltonian rewrites through the squared absolute Vandermonde product |
| `commutator_nonzero_and_dyson_bridge` | packet combining nonzero commutator and finite Dyson rewrite |
| `vandermonde_determinant_ne_zero_of_range_defect` | scalar Vandermonde determinant is nonzero |

## Non-Claims

This file does not prove Witten's unorientable parity anomaly, GUE asymptotics,
KMS/BEC physics, C*-completion, zeta-zero statistics, or RH consequences.  The
operator-to-scalar readout remains explicit proof-carrying data.
