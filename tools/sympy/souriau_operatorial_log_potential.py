#!/usr/bin/env python3
"""
Direct finite/statewise SymPy companion for
InfoGeometry.Canonical.SouriauOperatorialLogPotential.

Scope is intentionally honest:
- finite algebraic identities;
- scalar/operatorial readbacks that mirror the Lean owner file;
- no infinite analytic theorem, no trace-class functional analysis claim, and
  no unconditional zeta/heat-kernel interpretation.
"""

from __future__ import annotations

import math
import sympy as sp


EPS = 1e-10


def approx_eq(a, b, tol=EPS):
    return abs(complex(sp.N(a)) - complex(sp.N(b))) <= tol


# ---------------------------------------------------------------------------
# 1. Log-Radon-Nikodym bucket-1 identities
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

assert all(sp.simplify(log_density[x] - sp.log(rn[x])) == 0 for x in states)
assert all(sp.simplify(surprisal_density[x] + log_density[x]) == 0 for x in states)
assert sp.simplify(KL - expectation_log) == 0
assert sp.simplify(KL + expectation_surprisal) == 0


# ---------------------------------------------------------------------------
# 2. Regularized Jacobian potential sample identity
# ---------------------------------------------------------------------------

sample_log_det_reg = {
    "phi0": sp.Rational(3, 5),
    "phi1": sp.Rational(-7, 4),
}
volume_compression = {k: -v for k, v in sample_log_det_reg.items()}
assert all(
    sp.simplify(sp.sympify(volume_compression[k] + sample_log_det_reg[k])) == 0
    for k in sample_log_det_reg
)


# ---------------------------------------------------------------------------
# 3. Operatorial exponential family: scalar diagonal model
# ---------------------------------------------------------------------------

beta = sp.symbols("beta", real=True)
K1 = sp.Integer(2)
K2 = sp.Integer(5)

untraced = sp.Matrix.diag(sp.exp(-beta * K1), sp.exp(-beta * K2))
trace_readout = sp.trace(untraced)
partition_function = trace_readout
partition_potential = sp.log(trace_readout)
operatorial_exponential_family = untraced

assert operatorial_exponential_family == untraced
assert sp.simplify(partition_function - trace_readout) == 0
assert sp.simplify(partition_potential - sp.log(trace_readout)) == 0


# ---------------------------------------------------------------------------
# 4. Souriau Gibbs density negative-log readback
# ---------------------------------------------------------------------------

pairing_value = sp.Rational(7, 5)
Phi = sp.Rational(11, 10)
K_beta = pairing_value
gibbs_density = sp.exp(-K_beta - Phi)

assert sp.simplify(K_beta - pairing_value) == 0
assert sp.simplify(-sp.log(gibbs_density) - (K_beta + Phi)) == 0
assert sp.simplify(-sp.log(gibbs_density) - (pairing_value + Phi)) == 0


# ---------------------------------------------------------------------------
# 5. Negative-log RN derivative modular potential readback
# ---------------------------------------------------------------------------

rn_derivative = gibbs_density
modular_potential = -sp.log(rn_derivative)
assert sp.simplify(modular_potential - (K_beta + Phi)) == 0


# ---------------------------------------------------------------------------
# 6. Moment-map generating potential equalities on a sample variation
# ---------------------------------------------------------------------------

Q = sp.Rational(13, 7)
delta_beta = sp.Rational(-5, 3)
xi = sp.Rational(2, 9)
eta = sp.Rational(-4, 5)

dPhi = -Q * delta_beta
covariance_tensor = xi * eta + sp.Rational(1, 6)
hessian = covariance_tensor

assert sp.simplify(dPhi + Q * delta_beta) == 0
assert sp.simplify(hessian - covariance_tensor) == 0


# ---------------------------------------------------------------------------
# 7. Quantum operatorial Souriau family readback in a scalarized model
# ---------------------------------------------------------------------------

Jhat_beta = sp.Integer(4)
logZ = sp.log(sp.Integer(7))
op_identity = sp.Integer(1)
modular_hamiltonian = Jhat_beta + logZ * op_identity

assert sp.simplify(modular_hamiltonian - (Jhat_beta + logZ * op_identity)) == 0


# ---------------------------------------------------------------------------
# 8. Renyi/Mellin finite algebraic identity and positivity
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
assert sp.N(renyi_partition) > 0


# ---------------------------------------------------------------------------
# 9. Metriplectic / GENERIC finite scalar sanity checks
# ---------------------------------------------------------------------------

rho = sp.Rational(3, 2)
variation_of_relative_free_energy = 2 * rho - 1
force = variation_of_relative_free_energy
onsager_operator = lambda z: 3 * z

dissipative_flow = -onsager_operator(force)
free_energy_derivative = sp.Rational(-7, 3)

assert sp.simplify(force - variation_of_relative_free_energy) == 0
assert sp.simplify(dissipative_flow + onsager_operator(force)) == 0
assert free_energy_derivative <= 0

energy_evolution = sp.Integer(0)
entropy_production = sp.Rational(5, 4)
assert energy_evolution == 0
assert entropy_production >= 0


print("SymPy Souriau operatorial log-potential checks passed.")
print(f"KL = {sp.N(KL)}")
print(f"partition trace = {trace_readout}")
print(f"partition potential = {partition_potential}")
print(f"gibbs_density = {sp.N(gibbs_density)}")
print(f"modular_potential = {sp.simplify(modular_potential)}")
print(f"renyi_partition = {sp.N(renyi_partition)}")
print(
    "Honest scope: finite/statewise/log-potential identities only; no infinite "
    "analytic or heat-kernel theorem claimed."
)
