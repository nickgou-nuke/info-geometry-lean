import sympy as sp


x, y = sp.symbols("x y", real=True)


def T(p):
    return sp.Matrix([p[0], p[1] + 1])


def T_inv(p):
    return sp.Matrix([p[0], p[1] - 1])


def G(p):
    return sp.Matrix([p[0] + 1, -p[1]])


def M(p):
    return sp.Matrix([p[0], -p[1]])


def H(p):
    return sp.Matrix([-p[0], -p[1]])


p = sp.Matrix([x, y])
assert sp.simplify(G(T(p)) - T_inv(G(p))) == sp.zeros(2, 1)
assert sp.simplify(G(G(p)) - sp.Matrix([x + 2, y])) == sp.zeros(2, 1)
assert sp.simplify(M(M(p)) - p) == sp.zeros(2, 1)
assert sp.simplify(H(H(p)) - p) == sp.zeros(2, 1)
assert sp.simplify(G(p) - (M(p) + sp.Matrix([1, 0]))) == sp.zeros(2, 1)

print("KleinBottle.py: glide, mirror, and half-turn identities verified")
