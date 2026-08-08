import sympy as sp


beta = sp.symbols("beta", real=True)
m, n, p, k = sp.symbols("m n p k", positive=True, integer=True)


def arithmetic_energy(integer):
    return sp.log(integer)


def boltzmann_weight(inv_temp, integer):
    return sp.exp(-inv_temp * arithmetic_energy(integer))


def dirichlet_weight(inv_temp, integer):
    return integer ** (-inv_temp)


assert sp.simplify(arithmetic_energy(1)) == 0
assert sp.simplify(arithmetic_energy(m * n) - arithmetic_energy(m) - arithmetic_energy(n)) == 0
assert sp.simplify(arithmetic_energy(p**k) - k * arithmetic_energy(p)) == 0
assert sp.simplify(boltzmann_weight(beta, n) - dirichlet_weight(beta, n)) == 0
assert sp.simplify(
    boltzmann_weight(beta, m * n) - boltzmann_weight(beta, m) * boltzmann_weight(beta, n)
) == 0

for cutoff in range(1, 10):
    finite_trace = sum(boltzmann_weight(beta, j) for j in range(1, cutoff + 1))
    finite_zeta_trace = sum(dirichlet_weight(beta, j) for j in range(1, cutoff + 1))
    assert sp.simplify(finite_trace - finite_zeta_trace) == 0

occupation = {2: 3, 3: 1, 5: 2}
integer_state = sp.prod(prime ** exponent for prime, exponent in occupation.items())
occupation_energy = sum(exponent * sp.log(prime) for prime, exponent in occupation.items())
assert sp.simplify(sp.log(integer_state) - occupation_energy) == 0

print("ArithmeticHamiltonianZeta.py: arithmetic Hamiltonian finite trace identities verified")
