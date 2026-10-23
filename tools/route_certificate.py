"""Independent finite-route checks and proof-carrying Lean export.

The checker verifies local integer identities, without invoking Kahn peeling.
Lean independently checks the exported data and derives the Drazin witness and
its least possible exponent. This does not certify Python or the shell-rank
algorithm. Requires the FunctionalRouteCertificate addition to PR #194.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, fields
import json
from pathlib import Path
import re
from typing import Sequence

from .functional_route_fibers import RouteGeometry, analyze_route


@dataclass(frozen=True)
class RouteCertificate:
    route: tuple[int, ...]
    recurrent: tuple[int, ...]
    cycle: tuple[int, ...]
    inverse_cycle: tuple[int, ...]
    rho: tuple[int, ...]  # Indices in recurrent, not ambient token indices.
    depth: tuple[int, ...]
    bound: int


def _check_ints(name: str, values: Sequence[int], length: int,
                upper: int | None = None) -> None:
    if not isinstance(values, (tuple, list)) or len(values) != length:
        raise ValueError(f'{name} has the wrong container or length.')
    if any(type(v) is not int or v < 0 or (upper is not None and v >= upper)
           for v in values):
        raise ValueError(f'{name} must contain integers in the specified range.')


def validate_certificate(cert: RouteCertificate) -> None:
    """Check only local equations and an attained bound, in O(n+c) work.

    No graph traversal, matrix arithmetic, pseudoinverse, or trusted proof
    claim occurs here. Failure raises ValueError; success is not a Lean verdict.
    """
    if not isinstance(cert, RouteCertificate):
        raise ValueError('Expected a RouteCertificate.')
    if not isinstance(cert.route, (tuple, list)) or not cert.route:
        raise ValueError('The runtime certificate requires a nonempty route.')
    if not isinstance(cert.recurrent, (tuple, list)) or not cert.recurrent:
        raise ValueError('The recurrent coordinate set must be nonempty.')
    n, c = len(cert.route), len(cert.recurrent)
    _check_ints('route', cert.route, n, n)
    _check_ints('recurrent', cert.recurrent, c, n)
    _check_ints('cycle', cert.cycle, c, c)
    _check_ints('inverse_cycle', cert.inverse_cycle, c, c)
    _check_ints('rho', cert.rho, n, c)
    _check_ints('depth', cert.depth, n)
    if len(set(cert.recurrent)) != c:
        raise ValueError('Recurrent token indices must be distinct.')
    if type(cert.bound) is not int or cert.bound != max(cert.depth):
        raise ValueError('bound must equal the maximum attained depth.')
    for j, node in enumerate(cert.recurrent):
        if cert.inverse_cycle[cert.cycle[j]] != j or cert.cycle[cert.inverse_cycle[j]] != j:
            raise ValueError('Cycle maps must be mutual inverses.')
        if cert.rho[node] != j:
            raise ValueError('Retraction does not fix recurrent coordinates.')
        if cert.route[node] != cert.recurrent[cert.cycle[j]]:
            raise ValueError('Cycle action does not match the route.')
        if cert.depth[node] != 0:
            raise ValueError('Recurrent depth must be zero.')
    recurrent = set(cert.recurrent)
    for i, target in enumerate(cert.route):
        if cert.rho[target] != cert.cycle[cert.rho[i]]:
            raise ValueError('Retraction is not phase-synchronized.')
        if cert.depth[i] == 0 and i not in recurrent:
            raise ValueError('A zero-depth token is missing from the recurrent set.')
        if cert.depth[i] > 0 and cert.depth[target] + 1 != cert.depth[i]:
            raise ValueError('Positive depth must decrease by exactly one.')


def certificate_from_geometry(g: RouteGeometry) -> RouteCertificate:
    """Extract and independently check the graph fields of a computed result.

    peel_height, shell_ranks and cycle_count are deliberately not certified by
    this interface. The returned certificate covers the graph-to-Drazin data.
    """
    positions = {node: j for j, node in enumerate(g.recurrent)}
    try:
        cycle = tuple(positions[g.route[node]] for node in g.recurrent)
        rho = tuple(positions[node] for node in g.rho)
        inverse = [-1] * len(cycle)
        for j, target in enumerate(cycle):
            inverse[target] = j
        cert = RouteCertificate(g.route, g.recurrent, cycle, tuple(inverse), rho,
                                g.depth, g.index)
        validate_certificate(cert)
        expected_inverse = tuple(cert.recurrent[cert.inverse_cycle[j]] for j in cert.rho)
        if g.inverse_route != expected_inverse:
            raise ValueError('Computed inverse route disagrees with the certificate.')
        return cert
    except (KeyError, IndexError, TypeError) as exc:
        raise ValueError('Malformed graph data.') from exc


def certificate_from_route(route: Sequence[int]) -> RouteCertificate:
    return certificate_from_geometry(analyze_route(route))


def certificate_from_dict(payload: dict[str, object]) -> RouteCertificate:
    if not isinstance(payload, dict) or set(payload) != {f.name for f in fields(RouteCertificate)}:
        raise ValueError('Certificate JSON must have exactly the documented fields.')
    arrays = {}
    for field in fields(RouteCertificate):
        if field.name == 'bound':
            continue
        value = payload[field.name]
        if not isinstance(value, list):
            raise ValueError(f'{field.name} must be a JSON array.')
        arrays[field.name] = tuple(value)
    cert = RouteCertificate(**arrays, bound=payload['bound'])
    validate_certificate(cert)
    return cert


def emit_lean(cert: RouteCertificate, namespace: str = 'GeneratedRoute') -> str:
    """Emit data and kernel-reduced local proofs, never a claimed result file."""
    validate_certificate(cert)
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)*', namespace):
        raise ValueError('Use an ASCII Lean namespace with identifier components.')
    # Quoting also makes Lean keyword components valid identifiers.
    namespace = '.'.join(f'«{part}»' for part in namespace.split('.'))
    n, c = len(cert.route), len(cert.recurrent)
    vec = lambda values: '![' + ', '.join(map(str, values)) + ']'
    return f'''/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FunctionalRouteCertificate
import Mathlib.LinearAlgebra.Matrix.Notation

namespace {namespace}
open InfoGeometry.Routing.FunctionalRouteCertificate
open InfoGeometry.Routing.FunctionalRouteCore
open InfoGeometry.Canonical.Drazin
open DeterministicArgmaxAttention

def route : Fin {n} → Fin {n} := {vec(cert.route)}
def embed : Fin {c} → Fin {n} := {vec(cert.recurrent)}
def sigma : Equiv.Perm (Fin {c}) where
  toFun := {vec(cert.cycle)}
  invFun := {vec(cert.inverse_cycle)}
  left_inv := by decide
  right_inv := by decide
def rho : Fin {n} → Fin {c} := {vec(cert.rho)}
def depth : Fin {n} → ℕ := {vec(cert.depth)}

theorem local_certificate : LocalCertificate route embed sigma rho depth := by
  constructor <;> decide

theorem certified_inverse :
    IsDrazinInverse (deterministicAttention route)
      (deterministicAttention (inverseRoute embed sigma rho)) {cert.bound} :=
  certified_drazin local_certificate {cert.bound} (by decide)

theorem certified_minimum {{B : Matrix (Fin {n}) (Fin {n}) ℝ}} {{r : ℕ}}
    (hB : IsDrazinInverse (deterministicAttention route) B r) : {cert.bound} ≤ r :=
  minimum_witness_index local_certificate {cert.bound} (by decide) (by decide) hB

end {namespace}

#print axioms {namespace}.local_certificate
#print axioms {namespace}.certified_inverse
#print axioms {namespace}.certified_minimum
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--route', help='Comma-separated zero-based route targets')
    source.add_argument('--certificate', type=Path, help='Existing certificate JSON')
    parser.add_argument('--lean-out', type=Path, help='Write a Lean proof candidate')
    parser.add_argument('--namespace', default='GeneratedRoute')
    args = parser.parse_args()
    try:
        if args.route is not None:
            cert = certificate_from_route([int(x.strip()) for x in args.route.split(',')])
        else:
            cert = certificate_from_dict(json.loads(args.certificate.read_text(encoding='utf-8')))
        if args.lean_out is not None:
            args.lean_out.write_text(emit_lean(cert, args.namespace), encoding='utf-8')
        print(json.dumps(asdict(cert), indent=2))
    except (OSError, ValueError, TypeError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
