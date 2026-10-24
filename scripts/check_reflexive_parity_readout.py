#!/usr/bin/env python3
"""Exact regression-instance checks; arbitrary-ring Lean proofs are authoritative.

Run with /home/goutev/miniforge3/envs/sage/bin/python. Matrix seeds are read from
ReflexiveParityRegression.lean, not supplied by a different presentation.
"""
import hashlib
import json
from pathlib import Path
import re

import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
OWNER = "lean/InfoGeometry/Canonical/ReflexiveParityReadout.lean"
REGRESSION = "lean/InfoGeometry/Canonical/ReflexiveParityRegression.lean"
text = (ROOT / REGRESSION).read_text()


def seed(name):
    match = re.search(r"def " + name + r" : Matrix \(Fin 3\) \(Fin 3\) ℤ := !!\[([^]]+)\]", text)
    if match is None:
        raise ValueError(f"Native seed declaration not found: {name}")
    return sp.Matrix([[int(x.strip()) for x in row.split(",")]
                      for row in match[1].split(";")])


d, b = seed("d3"), seed("b3")
p, q = d*b, b*d
support, velocity, wheel, grading = p+q, d+b, d-b, p-q
unit = velocity + sp.eye(3) - support
alpha, beta, a, c = sp.symbols("alpha beta a c")
x = alpha*velocity + beta*wheel
rho = c*q + a*p


def zero(matrix):
    return all(sp.expand(entry) == 0 for entry in matrix)


checks = {
    "d_square_zero": zero(d*d),
    "b_square_zero": zero(b*b),
    "d_b_d": zero(d*b*d-d),
    "b_d_b": zero(b*d*b-b),
    "proper_support": support != sp.eye(3),
    "ambient_unit_square": zero(unit*unit-sp.eye(3)),
    "seed_swap_d": zero(unit*d*unit-b),
    "seed_swap_b": zero(unit*b*unit-d),
    "combination_conjugation": zero(unit*x*unit-(alpha*velocity-beta*wheel)),
    "combination_defect": zero(unit*x*unit-x+2*beta*wheel),
    "polarization_density": zero(grading*rho-(a*p-c*q)),
    "polarized_trace": sp.expand(sp.trace(grading*rho)-(a-c)) == 0,
    "mixed_element_round_trip": unit*(velocity+wheel)*unit == 2*b,
    "polarized_readout_five": sp.trace(grading*(4*q+9*p)) == 5,
}
assert all(checks.values()), checks
paths = [OWNER, REGRESSION, "lean/InfoGeometry/Canonical/GrassmannianBundleCyclotomicOrientability.lean",
         "lean/InfoGeometry/Core/PeirceDensityIntertwining.lean"]
result = {
    "scope": "Exact 3x3 integral regression instance, not the arbitrary-ring proof or paper geometry",
    "carrier": "Matrix (Fin 3) (Fin 3) Z",
    "basis_order": ["e0", "e1", "e2"],
    "matrix_convention": "row-major storage, column-vector action, ordinary left-to-right product",
    "anti_hom": False,
    "lean_owner": "InfoGeometry.Canonical.ReflexiveParityReadout",
    "round_trip": {
        "input": "transitionVelocity d3 b3 + wheelGenerator d3 b3",
        "output": [[0, 0, 0], [2, 0, 0], [0, 0, 0]],
        "lean_theorem": "InfoGeometry.Canonical.ReflexiveParityRegression.mixed_element_nonzero_defect",
    },
    "round_trip_verified": True,
    "checks": checks,
    "source_sha256": {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
print(json.dumps(result, indent=2, sort_keys=True))
