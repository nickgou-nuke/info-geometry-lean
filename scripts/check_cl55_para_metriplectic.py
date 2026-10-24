#!/usr/bin/env python3
"""Exact supplementary checks for the native Cl55 para/metriplectic owners.

Basis: (x0,...,x4,xi0,...,xi4) in neutral coordinates, then
(p0,...,p4,n0,...,n4) on Clifford55.V55. Column vectors; AB = A after B.
Duality B.toDual sends v to the covector column B.T*v, not B*v.
The script is independent arithmetic evidence, not a parser or Lean proof.
"""
import hashlib
import json
from pathlib import Path

import sympy as s

ROOT = Path(__file__).resolve().parents[1]
OWNERS = [
    "Clifford/NeutralPhaseSpaceCore.lean",
    "Clifford/PhaseSpaceGeneralizedMetric.lean",
    "Clifford/Cl55NeutralHyperbolicIsometry.lean",
    "Clifford/ParaKahler55SUSYClosure.lean",
    "Clifford/ParaKahlerGeneralizedMetric.lean",
    "Clifford/Cl55ParaKahlerMetric.lean",
    "Clifford/Cl55MetriplecticReduction.lean",
    "Clifford/Cl55ParaKahlerPinTransport.lean",
    "Thermo/GenericMetriplecticFlow.lean",
    "Thermo/BilinearMetriplecticReduction.lean",
]


def main():
    eye, zero = s.eye(5), s.zeros(5)
    block = lambda a, b, c, d: a.row_join(b).col_join(c.row_join(d))
    B = block(zero, eye, eye, zero)
    K = block(eye, zero, zero, -eye)
    S = B
    J = K * S
    omega = -B * K
    change = block(eye, eye, eye, -eye) / 2
    inverse = change.inv()
    q = block(eye, zero, zero, -eye)
    omega55 = inverse.T * omega * inverse
    H55 = inverse.T * B * S * inverse
    k55 = change * K * inverse
    e = lambda i: s.eye(10)[:, i]
    P = s.diag(*[int(i in (1, 6)) for i in range(10)])
    C = s.diag(*[int(i in (0, 5)) for i in range(10)])
    L = P * omega55.T.inv() * P.T
    M = C * H55.T.inv() * C.T
    dH, dS = omega55.T * e(1), H55.T * e(0)
    flow = L * dH + M * dS
    reflection = s.diag(*[(-1 if i == 5 else 1) for i in range(10)])
    checks = {
        "K_squared": K * K == s.eye(10),
        "K_S_anticommute": K * S == -S * K,
        "phase_squared": J * J == -s.eye(10),
        "reflected_phase_twin": S * J * S == -J,
        "neutral_to_Q55": change.T * q * change == B / 2,
        "K55_is_existing_swap": k55 == S,
        "omega55_para_sign": omega55 == -2 * q * k55,
        "positive_metric": H55 == 2 * s.eye(10),
        "negative_polar_witness": (e(5).T * (2 * q) * e(5))[0] == -2,
        "reversible_skew": L.T == -L,
        "dissipative_symmetric": M.T == M,
        "dissipative_nonnegative": all(x >= 0 for x in M.diagonal()),
        "entropy_casimir": L * dS == s.zeros(10, 1),
        "energy_casimir": M * dH == s.zeros(10, 1),
        "reversible_nonzero": L * dH == e(1),
        "dissipative_nonzero": M * dS == e(0),
        "energy_rate": (dH.T * flow)[0] == 0,
        "entropy_rate": (dS.T * flow)[0] == 2,
        "reflection_positive_metric": reflection.T * H55 * reflection == H55,
        "reflection_not_symplectic": reflection.T * omega55 * reflection != omega55,
        "reflection_not_antisymplectic": reflection.T * omega55 * reflection != -omega55,
        "transported_para_structure":
            reflection.T * omega55 * reflection == -2 * q * (reflection * k55 * reflection),
    }
    assert all(checks.values()), checks
    print(json.dumps({
        "scope": "Independent finite rational arithmetic; Lean is proof authority",
        "basis_order": [f"p{i}" for i in range(5)] + [f"n{i}" for i in range(5)],
        "operator_order": "AB = A after B; bilinear toDual matrix = B.T",
        "round_trip": {
            "neutral_x0": list(map(str, change * e(0))),
            "recovered": list(map(str, inverse * change * e(0))),
        },
        "checks": checks,
        "source_sha256": {
            p: hashlib.sha256((ROOT / "lean/InfoGeometry" / p).read_bytes()).hexdigest()
            for p in OWNERS
        },
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
