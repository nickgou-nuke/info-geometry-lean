"""SymPy witness: Fibonacci anyon seed -> osp/sl2 lanes -> Cl(1,1) atom.

This complements `FibonacciCliffordBridge.lean`:
- verifies the golden identity phi^2 = phi + 1;
- encodes tau fusion at the dimension level;
- maps tau to the tripotent Witten grading sigma3;
- checks the toy osp(1|2) even-generator dictionary;
- checks the local K N A supertrace and pure squeeze limit;
- checks a two-neighbour Clifford-atom tensor channel.
"""

import sympy as sp


def assert_zero(name, expr):
    simplified = sp.simplify(sp.expand_func(expr).rewrite(sp.exp))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")


def assert_matrix_zero(name, M):
    S = M.applyfunc(lambda x: sp.simplify(sp.expand_func(x).rewrite(sp.exp)))
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
assert_zero("golden identity", phi**2 - phi - 1)
assert_zero("tau fusion dimension", phi**2 - (1 + phi))

I2 = sp.eye(2)
sigma3 = sp.Matrix([[1, 0], [0, -1]])
i_sigma2 = sp.Matrix([[0, 1], [-1, 0]])
sigma_plus = sp.Matrix([[0, 1], [0, 0]])

# Fibonacci tau -> Clifford/Witten tripotent.
assert_matrix_zero("tau -> sigma3 tripotent", sigma3**3 - sigma3)

# Toy osp(1|2) even lanes reduced to the Clifford atom.
assert_matrix_zero("rotation square", i_sigma2**2 + I2)
assert_matrix_zero("boost square", sigma3**2 - I2)
assert_matrix_zero("boost/rotation anticommute", sigma3 * i_sigma2 + i_sigma2 * sigma3)
assert_matrix_zero("nilpotent square", sigma_plus**2)

# Atomic KNA Witten index.
theta, alpha, n = sp.symbols("theta alpha n", real=True)
K = sp.Matrix([[sp.cos(theta), -sp.sin(theta)], [sp.sin(theta), sp.cos(theta)]])
N = sp.Matrix([[1, n], [0, 1]])
A = sp.diag(sp.exp(alpha), sp.exp(-alpha))
KNA = sp.simplify(K * N * A)
STr = sp.trace(sigma3 * KNA)
assert_zero(
    "atomic supertrace",
    STr - (2 * sp.sinh(alpha) * sp.cos(theta) - n * sp.exp(-alpha) * sp.sin(theta)),
)
assert_zero("pure squeeze", STr.subs({theta: 0, n: 0}) - 2 * sp.sinh(alpha))

# Two neighbouring Clifford atoms.
two_parity = sp.kronecker_product(sigma3, sigma3)
two_nilpotent = sp.kronecker_product(sigma_plus, sigma_plus)
assert_matrix_zero("two atom parity square", two_parity**2 - sp.eye(4))
assert_matrix_zero("two atom nilpotent square", two_nilpotent**2)

# Finite prime-labelled tensor index witness.
a2, a3, a5 = sp.symbols("a2 a3 a5", real=True)
finite_prime_index = sp.prod(2 * sp.sinh(a) for a in [a2, a3, a5])
expected_prime_index = (2 * sp.sinh(a2)) * (2 * sp.sinh(a3)) * (2 * sp.sinh(a5))
assert_zero("finite prime atom index", finite_prime_index - expected_prime_index)

print("OK Fibonacci -> Clifford atom bridge SymPy witness completed")
