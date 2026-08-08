import sympy as sp


beta = sp.symbols("beta")
z = sp.symbols("z", nonzero=True)

bosonic_partition = z
fermionic_partition = 1 / z
total_susy_partition = bosonic_partition * fermionic_partition
assert sp.simplify(total_susy_partition - 1) == 0

laurent_pole_partition = 1 / (beta - 1)
mobius_fermion_regulator = beta - 1
assert sp.simplify(laurent_pole_partition * mobius_fermion_regulator - 1) == 0

pole_log_potential = -sp.log(beta - 1)
first_derivative = sp.diff(pole_log_potential, beta)
second_derivative = sp.diff(first_derivative, beta)

assert sp.simplify(first_derivative + 1 / (beta - 1)) == 0
assert sp.simplify(second_derivative - 1 / (beta - 1) ** 2) == 0

print("PhaseTransition_SUSY.py: SUSY regulator and pole curvature verified")
