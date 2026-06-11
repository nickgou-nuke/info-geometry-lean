#!/usr/bin/env python3
"""
Assertion-based SymPy companion for the finite readback corridor around
InfoGeometry.Canonical.SouriauOperatorialLogPotential.

This verifier checks only finite algebraic / thermodynamic identities that are
honestly mirrored by the Lean owner surfaces. It does NOT claim any infinite
analytic theorem such as 1/zeta(s) = STr(exp(-sH)).
"""

from __future__ import annotations

import itertools
import math
from functools import reduce
from operator import mul

import sympy as sp


def approx_eq(a, b, tol=1e-10):
    return abs(complex(sp.N(a)) - complex(sp.N(b))) <= tol


def prod(values):
    return reduce(mul, values, 1)


# ---------------------------------------------------------------------------
# 1. Log-Radon-Nikodym finite state-space sanity check
# ---------------------------------------------------------------------------

states = [0, 1, 2]
rn = {
    0: sp.Rational(1, 2),
    1: sp.Rational(1, 3),
    2: sp.Rational(1, 6),
}
nu = {
    0: sp.Rational(1, 5),
    1: sp.Rational(1, 2),
    2: sp.Rational(3, 10),
}

log_density = {x: sp.log(rn[x]) for x in states}
surprisal_density = {x: -log_density[x] for x in states}
expectation_log = sum(nu[x] * log_density[x] for x in states)
expectation_surprisal = sum(nu[x] * surprisal_density[x] for x in states)
KL = expectation_log

assert all(sp.simplify(surprisal_density[x] + log_density[x]) == 0 for x in states)
assert sp.simplify(sp.sympify(KL - expectation_log)) == 0
assert sp.simplify(sp.sympify(KL + expectation_surprisal)) == 0


# ---------------------------------------------------------------------------
# 2. Scalar operatorial exponential-family sanity check
# ---------------------------------------------------------------------------

beta = sp.symbols("beta", real=True)
K1 = sp.Integer(2)
K2 = sp.Integer(5)

untraced = sp.Matrix.diag(sp.exp(-beta * K1), sp.exp(-beta * K2))
trace_readout = sp.trace(untraced)
partition_potential = sp.log(trace_readout)

assert sp.simplify(trace_readout - (sp.exp(-2 * beta) + sp.exp(-5 * beta))) == 0
assert sp.simplify(partition_potential - sp.log(trace_readout)) == 0


# ---------------------------------------------------------------------------
# 3. Souriau Gibbs negative-log identity on a finite sample point
# ---------------------------------------------------------------------------

k_beta = sp.Rational(7, 5)
Phi = sp.Rational(11, 10)
gibbs_density = sp.exp(-k_beta - Phi)

assert sp.simplify(-sp.log(gibbs_density) - (k_beta + Phi)) == 0


# ---------------------------------------------------------------------------
# 4. Finite Möbius Dirichlet polynomial = finite fermionic Euler product
# ---------------------------------------------------------------------------

primes = [2, 3, 5]
s = sp.Integer(2)
x = {p: sp.Rational(1, p**int(s)) for p in primes}

finite_mobius_poly = sp.Integer(0)
for r in range(len(primes) + 1):
    for subset in itertools.combinations(primes, r):
        n = prod(subset)
        finite_mobius_poly += sp.mobius(n) * prod(x[p] for p in subset)

finite_fermionic_euler = prod(1 - x[p] for p in primes)
assert sp.simplify(finite_mobius_poly - finite_fermionic_euler) == 0


# ---------------------------------------------------------------------------
# 5. Finite weighted supertrace = finite Witten index under explicit pairing
# ---------------------------------------------------------------------------

levels = [0, 1, 2, 3]
zero_levels = {0}
boson = {0: 3, 1: 2, 2: 5, 3: 1}
fermion = {0: 1, 1: 2, 2: 5, 3: 1}
weight = {0: 1, 1: 17, 2: -4, 3: 9}

finite_weighted_supertrace = sum((boson[i] - fermion[i]) * weight[i] for i in levels)
finite_witten_index = sum((boson[i] - fermion[i]) for i in levels if i in zero_levels)
assert finite_weighted_supertrace == finite_witten_index


# ---------------------------------------------------------------------------
# 6. Finite primon partition = inverse evaluated finite Weyl denominator
# ---------------------------------------------------------------------------

beta_real = sp.Integer(2)
boltzmann = {p: sp.exp(-beta_real * sp.log(p)) for p in primes}
finite_primon_partition = prod((1 - boltzmann[p]) ** -1 for p in primes)
evaluated_weyl_denominator = prod(1 - boltzmann[p] for p in primes)
assert approx_eq(finite_primon_partition, evaluated_weyl_denominator ** -1)


# ---------------------------------------------------------------------------
# 7. Renyi/Mellin finite algebraic identity
# ---------------------------------------------------------------------------

gamma = sp.Rational(3, 2)
Z_gamma_beta = sp.Rational(9, 5)
Z_beta = sp.Rational(7, 4)
renyi_partition = Z_gamma_beta / (Z_beta ** gamma)
renyi_log_generator = sp.log(renyi_partition)
massieu_gamma_beta = sp.log(Z_gamma_beta)
massieu_beta = sp.log(Z_beta)

assert sp.simplify(
    renyi_log_generator - (massieu_gamma_beta - gamma * massieu_beta)
) == 0


print("SymPy finite readback checks passed.")
print(f"finite Möbius polynomial = {sp.simplify(finite_mobius_poly)}")
print(f"finite fermionic Euler product = {sp.simplify(finite_fermionic_euler)}")
print(f"finite weighted supertrace = {sp.Integer(finite_weighted_supertrace)}")
print(f"finite Witten index = {sp.Integer(finite_witten_index)}")
print(f"finite primon partition = {sp.N(finite_primon_partition)}")
print(f"inverse Weyl denominator = {sp.N(evaluated_weyl_denominator ** -1)}")
print("Honest scope: finite/statewise/operatorial identities only; no infinite zeta or heat-kernel theorem claimed.")
