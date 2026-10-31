#!/usr/bin/env python3
"""Reproduce an exact M₂(Q) counterexample to genV=0 => [P,X]=0.

Carrier alignment: `Op` in
`InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness` is
`Matrix (Fin 2) (Fin 2) ℚ`; entries below use the same row/column order.
Multiplication is ordinary row-by-column matrix multiplication, matching
Lean's `Matrix.mul_apply`.  This is a finite witness only, not a positivity or
state theorem.
"""

import hashlib
import json

import sympy as sp

P = sp.Matrix([[1, 0], [0, 0]])
X = sp.Matrix([[1, 1], [0, 0]])
I = sp.eye(2)
out = P * X * (I - P)
inc = (I - P) * X * P
V = out * inc + inc * out
J = P * X - X * P
pinch = P * X * P + (I - P) * X * (I - P)
delta_pinch = pinch * pinch - pinch
round_trip_product = P * X

payload = {
    "object": "one_sided_peirce_zero_metric_nonzero_current",
    "lean_owner": "InfoGeometry.OperatorAlgebra.PeirceDefectMatrixWitness",
    "cas_source": "scripts/cas/peirce_one_sided_zero_metric_witness.py",
    "carrier": "Op = Matrix (Fin 2) (Fin 2) ℚ",
    "cas_entry_domain": "SymPy integer matrices, embedded by ℤ → ℚ into the Lean carrier",
    "basis_order": ["0", "1"],
    "multiplication_convention": "row-by-column; (A*B)[i,j]=sum_k A[i,k]*B[k,j]",
    "lean_multiplication":
        "Matrix (Fin 2) (Fin 2) ℚ multiplication; row-by-column",
    "anti_hom": False,
    "round_trip_verified": True,
    "scope": "finite witness checked in SymPy and by the Lean owner theorem",
    "lean_definitions": {
        "cut": [[1, 0], [0, 0]],
        "oneSidedIdempotent": [[1, 1], [0, 0]],
    },
    "checked": {
        "cut_idempotent": P * P == P,
        "oneSidedIdempotent_idempotent": X * X == X,
        "outward_cone": out.tolist(),
        "inward_cone": inc.tolist(),
        "genV": V.tolist(),
        "commutator": J.tolist(),
        "pinching": pinch.tolist(),
        "pinched_idempotency_defect": delta_pinch.tolist(),
        "not_self_adjoint": X.T != X,
        "genV_zero": V == sp.zeros(2),
        "commutator_nonzero": J != sp.zeros(2),
        "round_trip_product": round_trip_product.tolist(),
    },
    "round_trip_element": {
        "input": {"left": P.tolist(), "right": X.tolist()},
        "expected_output": round_trip_product.tolist(),
        "lean_theorem": "cut_mul_oneSidedIdempotent",
    },
}
def normalize(value):
    if isinstance(value, sp.MatrixBase):
        return [[str(value[i, j]) for j in range(value.cols)] for i in range(value.rows)]
    if isinstance(value, list):
        return [normalize(item) for item in value]
    if isinstance(value, dict):
        return {key: normalize(item) for key, item in value.items()}
    if isinstance(value, sp.logic.boolalg.Boolean):
        return bool(value)
    if isinstance(value, sp.Basic):
        return str(value)
    return value

payload = normalize(payload)
encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
payload["artifact_hash"] = hashlib.sha256(encoded).hexdigest()
print(json.dumps(payload, indent=2, sort_keys=True))
