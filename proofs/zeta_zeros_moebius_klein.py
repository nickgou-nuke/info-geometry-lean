import sympy as sp


a, b = sp.symbols("a b", real=True)
s = a + sp.I * b


def involution(z):
    return 1 - z


assert sp.simplify(involution(involution(s)) - s) == 0
assert sp.simplify(sp.re(involution(s)) - (1 - a)) == 0
assert sp.solve(sp.Eq(1 - a, a), a)[0] == sp.Rational(1, 2)
assert sp.Rational(1, 2) == sp.Rational(0 + 1, 2)

zeta_s, chi_s, zeta_inv = sp.symbols("zeta_s chi_s zeta_inv")
functional_equation = sp.Eq(zeta_s, chi_s * zeta_inv)
assert functional_equation.subs(zeta_inv, 0).rhs == 0

u, v = sp.symbols("u v", real=True)
potential = u**2 + v**2
assert potential.subs({u: 0, v: 0}) == 0
assert sp.simplify(potential - 0) == u**2 + v**2

print("zeta_zeros_moebius_klein.py: Möbius involution and potential identities verified")
