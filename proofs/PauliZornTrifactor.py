import sympy as sp


t, x, y, z = sp.symbols("t x y z", real=True)
I = sp.I


def pauli_hermitian(t, x, y, z):
    return sp.Matrix([[t + z, x - I * y], [x + I * y, t - z]])


V = pauli_hermitian(t, x, y, z)
minkowski = t**2 - x**2 - y**2 - z**2

assert sp.simplify(V.det() - minkowski) == 0


def det_sector(delta):
    if sp.simplify(delta) == 0:
        return "parabolic/null"
    if delta.is_positive:
        return "elliptic/timelike"
    if delta.is_negative:
        return "hyperbolic/spacelike"
    return "symbolic"


E = sp.Matrix([[0, -1], [1, 0]])
H = sp.Matrix([[0, 1], [1, 0]])
N = sp.Matrix([[0, 1], [0, 0]])
I2 = sp.eye(2)

assert E.det() == 1 and E**2 == -I2
assert H.det() == -1 and H**2 == I2
assert N.det() == 0 and N**2 == sp.zeros(2)

OP = sp.symbols("OP")
assert sp.expand(OP**3 - OP) == sp.expand(OP * (OP - 1) * (OP + 1))


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def zorn_det(alpha, p, q, beta):
    return sp.simplify(alpha * beta - dot(p, q))


p = (x, y, z)
assert sp.simplify(zorn_det(t, p, p, t) - minkowski) == 0

# Null Pauli 4-vectors become determinant-null Zorn paravectors.
lightlike = {t: sp.sqrt(x**2 + y**2 + z**2)}
assert sp.simplify(zorn_det(t, p, p, t).subs(lightlike)) == 0

# Pure off-diagonal Zorn parafermions are square-zero in the Zorn product;
# this was fully checked in ZornOPParavector.py.  Here we keep the determinant
# link to the Pauli null cone.
assert zorn_det(0, p, (0, 0, 0), 0) == 0
assert zorn_det(0, (0, 0, 0), p, 0) == 0

print("PauliZornTrifactor.py: Pauli determinant, OP trifactor, and Zorn null embedding verified")
