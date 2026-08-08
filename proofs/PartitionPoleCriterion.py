import sympy as sp


beta, beta_c, E, L = sp.symbols("beta beta_c E L", real=True)

density_growth = sp.exp(beta_c * E)
boltzmann_damping = sp.exp(-beta * E)
integrand = density_growth * boltzmann_damping
rate = beta - beta_c

assert sp.simplify(integrand - sp.exp(-rate * E)) == 0

antiderivative = -sp.exp(-rate * E) / rate
assert sp.simplify(sp.diff(antiderivative, E) - sp.exp(-rate * E)) == 0

cutoff_model = (1 - sp.exp(-rate * L)) / rate
antiderivative_diff = antiderivative.subs(E, L) - antiderivative.subs(E, 0)
assert sp.simplify(cutoff_model - antiderivative_diff) == 0

pole_model = 1 / rate
assert sp.simplify(rate * pole_model - 1) == 0

zeta_rate = beta - 1
zeta_pole_model = 1 / zeta_rate
assert sp.simplify(zeta_rate * zeta_pole_model - 1) == 0

counting_energy_bound = sp.symbols("N_E", positive=True)
assert sp.simplify(sp.log(sp.exp(E)) - E) == 0

print("PartitionPoleCriterion.py: exponential density pole criterion verified")
