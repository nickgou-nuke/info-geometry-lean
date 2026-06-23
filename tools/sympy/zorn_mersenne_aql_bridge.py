#!/usr/bin/env python3
"""Finite discrete-to-Zorn bridge and AQL artifact generator.

This script mirrors `lean/InfoGeometry/Algebra/Zorn/DiscreteColorBridge.lean`
and the existing finite owner corridor in
`lean/InfoGeometry/Algebra/Zorn/G2TrifactorSU3.lean`.

Closed finite scope only:
* `3 + 7 + 127 = 137`
* `M2 = 3` matches the Zorn color-slot cardinality
* emit an AQL schema/instance text artifact and matching JSON payload

Negative scope:
* no `SU(3)` stabilizer theorem
* no global `G2` automorphism theorem
* no physics promotion
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AQL_PATH = ROOT / "formalization" / "aql" / "zorn_mersenne_color_bridge.aql"
JSON_PATH = ROOT / "formalization" / "aql" / "zorn_mersenne_color_bridge.json"

MERSENNE = {"m2": 3, "m3": 7, "m7": 127}
COUPLING_137 = 137
COLOR_SLOT_DIM = 3
TRIPOTENT_EIGENVALUES = [1, -1, 0]


def verify_packet() -> None:
    assert sum(MERSENNE.values()) == COUPLING_137
    assert MERSENNE["m2"] == COLOR_SLOT_DIM
    assert sorted(TRIPOTENT_EIGENVALUES) == [-1, 0, 1]


def json_payload() -> dict[str, object]:
    return {
        "source_schema": {
            "MersenneMode": ["m2", "m3", "m7"],
            "CouplingConstant": ["alpha_inv"],
            "prime_index": {"m2": 2, "m3": 3, "m7": 7},
            "dimension": MERSENNE,
            "value": {"alpha_inv": COUPLING_137},
        },
        "target_schema": {
            "ZornSlot": ["color", "anticolor", "diag_plus", "diag_minus"],
            "slot_dim": {
                "color": 3,
                "anticolor": 3,
                "diag_plus": 1,
                "diag_minus": 1,
            },
            "TripotentEigenvalue": [1, -1, 0],
        },
        "mapping": {
            "m2_to_slot": "color",
            "m2_to_anticolor": "anticolor",
            "m3_interpretation": "seven_imaginary_units_packet",
            "m7_interpretation": "127_degree_packet",
        },
        "scope": {
            "is_su3_theorem": False,
            "is_g2_classification": False,
            "is_physics_promotion": False,
        },
    }


def aql_text() -> str:
    return """/* Finite discrete-to-Zorn bridge. Textual artifact only. */

schema CombinatorialHierarchy = {
  entities
    MersenneMode
    CouplingConstant
  attributes
    prime_index : MersenneMode -> Integer
    dimension   : MersenneMode -> Integer
    value       : CouplingConstant -> Integer
}

schema ZornProjectorGeometry = {
  entities
    ZornSlot
    TripotentEigenvalue
  attributes
    slot_dim   : ZornSlot -> Integer
    eigen_val  : TripotentEigenvalue -> Integer
}

mapping HierarchyToGeometry = literal : CombinatorialHierarchy -> ZornProjectorGeometry {
  entity
    MersenneMode -> ZornSlot
  attributes
    dimension -> slot_dim
}

instance Exact137Data = literal : CombinatorialHierarchy {
  generators
    m2 m3 m7 : MersenneMode
    alphaInv : CouplingConstant
  equations
    prime_index(m2) = 2
    prime_index(m3) = 3
    prime_index(m7) = 7
    dimension(m2) = 3
    dimension(m3) = 7
    dimension(m7) = 127
    value(alphaInv) = 137
}

/* Honest scope boundary:
   - M2=3 maps to the finite Zorn color-slot cardinality.
   - This artifact does NOT prove an SU(3) stabilizer theorem or a G2 classification.
*/
"""


def main() -> None:
    verify_packet()
    payload = json_payload()
    AQL_PATH.parent.mkdir(parents=True, exist_ok=True)
    AQL_PATH.write_text(aql_text(), encoding="utf-8")
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    print("ZORN_MERSENNE_AQL_BRIDGE_OK")
    print(json.dumps({
        "sum_3_7_127": sum(MERSENNE.values()),
        "color_slot_dim": COLOR_SLOT_DIM,
        "tripotent_eigenvalues": TRIPOTENT_EIGENVALUES,
        "aql_path": str(AQL_PATH),
        "json_path": str(JSON_PATH),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
