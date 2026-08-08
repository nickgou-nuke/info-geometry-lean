import sympy as sp


beta, tau, K = sp.symbols("beta tau K", real=True)
beta2, tau2 = sp.symbols("beta2 tau2", real=True)
I = sp.I

eps = beta + I * tau
eps2 = beta2 + I * tau2

assert sp.simplify((1 + I * 0) - 1) == 0
assert sp.simplify((0 + I * 1) - I) == 0
assert sp.simplify(((beta + beta2) + I * (tau + tau2)) - (eps + eps2)) == 0

lhs_exp_arg = sp.expand((eps + eps2) * K)
rhs_exp_arg = sp.expand(eps * K + eps2 * K)
assert sp.simplify(lhs_exp_arg - rhs_exp_arg) == 0

master_density_at_zero = sp.exp(0 * K) - 1 - 0 * K
assert sp.simplify(master_density_at_zero) == 0

print("SouriauComplexTemperature.py: complex beta-vector identities verified")
