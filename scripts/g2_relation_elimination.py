"""Exact elimination witnesses for SpinorialCore.G2.relation.

Read the owner's adjacency table verbatim; basis is Fin 12 in ascending order,
rows first. No floating point or permutation determinant enumeration is used.
The JSON is reproducible evidence, not a Lean proof.
"""
import hashlib
import json
import re
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OWNER = "lean/InfoGeometry/Canonical/SpinorialCore/G2Certificate.lean"


def certificate():
    source = (ROOT / OWNER).read_text()
    table = re.search(r"def adjacency.*?!!\[(.*?)\]", source, re.S).group(1)
    adjacency = sp.Matrix([
        [int(x.strip()) for x in row.split(",")] for row in table.split(";")
    ])
    relation = sp.eye(12) - adjacency
    lower, upper, swaps = relation.LUdecomposition()
    assert swaps == [[5, 6]]
    inverse = lower.inv()
    scales = [sp.ilcm(*[x.q for x in inverse.row(i)]) for i in range(12)]
    elimination = sp.diag(*scales) * inverse
    triangular = sp.diag(*scales) * upper
    permuted = relation.copy()
    permuted.row_swap(5, 6)
    assert elimination * permuted == triangular
    assert elimination.is_lower and triangular.is_upper
    assert relation[0, 1] == -1 and permuted[5, 0] == -1
    det_e = sp.prod(elimination.diagonal())
    det_t = sp.prod(triangular.diagonal())
    assert det_t == 1456 * det_e
    return {
        "lean_owner": "InfoGeometry.Canonical.SpinorialCore.G2.relation",
        "carrier": "Matrix (Fin 12) (Fin 12) Int",
        "basis_order": list(range(12)),
        "orientation": "row-major; left multiplication; swap rows 5 and 6",
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "cas_source": "scripts/g2_relation_elimination.py",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "checked": ["elimination_product", "lower_triangular", "upper_triangular", "diagonal_products"],
        "round_trip": {"relation_0_1": -1, "swapped_relation_5_0": -1},
        "round_trip_verified": True,
        "lean_round_trip_theorem": "InfoGeometry.Canonical.SpinorialCore.G2.elimination_basis_alignment",
        "elimination": [[int(x) for x in row] for row in elimination.tolist()],
        "triangular": [[int(x) for x in row] for row in triangular.tolist()],
        "diagonal_products": [int(det_e), int(det_t)],
    }


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2, sort_keys=True))
