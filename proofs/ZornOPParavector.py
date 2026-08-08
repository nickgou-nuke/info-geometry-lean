import sympy as sp


def vec(x, y, z):
    return sp.Matrix([x, y, z])


def dot(u, v):
    return (u.T * v)[0]


def cross(u, v):
    return sp.Matrix(
        [
            u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0],
        ]
    )


class Zorn:
    """Zorn vector matrix [[a, u], [v, b]]."""

    def __init__(self, a, u, v, b):
        self.a = sp.simplify(a)
        self.u = sp.Matrix(u)
        self.v = sp.Matrix(v)
        self.b = sp.simplify(b)

    def __mul__(self, other):
        a, u, v, b = self.a, self.u, self.v, self.b
        c, x, y, d = other.a, other.u, other.v, other.b
        return Zorn(
            a * c + dot(u, y),
            a * x + d * u - cross(v, y),
            c * v + b * y + cross(u, x),
            dot(v, x) + b * d,
        )

    def __sub__(self, other):
        return Zorn(self.a - other.a, self.u - other.u, self.v - other.v, self.b - other.b)

    def __eq__(self, other):
        d = self - other
        return (
            sp.simplify(d.a) == 0
            and sp.simplify(d.b) == 0
            and all(sp.simplify(x) == 0 for x in d.u)
            and all(sp.simplify(x) == 0 for x in d.v)
        )

    def det(self):
        return sp.simplify(self.a * self.b - dot(self.u, self.v))


zero3 = vec(0, 0, 0)
one = Zorn(1, zero3, zero3, 1)
zero = Zorn(0, zero3, zero3, 0)


# Orthogonal primitive projectors: OP^2=OP, hence OP^3=OP.
E_plus = Zorn(1, zero3, zero3, 0)
E_minus = Zorn(0, zero3, zero3, 1)

assert E_plus * E_plus == E_plus
assert E_minus * E_minus == E_minus
assert E_plus * E_plus * E_plus == E_plus
assert E_minus * E_minus * E_minus == E_minus
assert E_plus.det() == 0
assert E_minus.det() == 0


# Paravector/null lanes: off-diagonal Zorn matrices square to zero.
x, y, z = sp.symbols("x y z")
u = vec(x, y, z)
N_up = Zorn(0, u, zero3, 0)
N_down = Zorn(0, zero3, u, 0)

assert N_up * N_up == zero
assert N_down * N_down == zero
assert N_up.det() == 0
assert N_down.det() == 0


# Mixed products recover rank-one scalar projectors through dot products.
M = N_up * N_down
assert M.a == dot(u, u)
assert M.b == 0
assert M.det() == 0


def cubic_classifier(Z):
    if Z * Z == zero:
        return "parabolic/nilpotent"
    if Z * Z * Z == Z:
        return "trifactor/projector"
    return "generic"


assert cubic_classifier(E_plus) == "trifactor/projector"
assert cubic_classifier(N_up) == "parabolic/nilpotent"

print("ZornOPParavector.py: Zorn projectors OP^3=OP and paravector nilpotents verified")
