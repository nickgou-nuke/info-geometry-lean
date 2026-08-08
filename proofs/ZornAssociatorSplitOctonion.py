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

    def is_zero(self):
        return (
            sp.simplify(self.a) == 0
            and sp.simplify(self.b) == 0
            and all(sp.simplify(c) == 0 for c in self.u)
            and all(sp.simplify(c) == 0 for c in self.v)
        )

    def det(self):
        return sp.simplify(self.a * self.b - dot(self.u, self.v))


zero3 = vec(0, 0, 0)
e1 = vec(1, 0, 0)
e2 = vec(0, 1, 0)
e3 = vec(0, 0, 1)


def U(u):
    return Zorn(0, u, zero3, 0)


def L(v):
    return Zorn(0, zero3, v, 0)


def associator(A, B, C):
    return (A * B) * C - A * (B * C)


# Pure upper and pure lower lanes are individually exterior/nilpotent and
# associative on repeated arguments.
assert (U(e1) * U(e1)).is_zero()
assert associator(U(e1), U(e1), U(e2)).is_zero()
assert associator(U(e1), U(e2), U(e2)).is_zero()

# But mixed Zorn lanes have a genuine non-associative associator.
A = U(e1)
B = L(e1)
C = U(e2)
assoc = associator(A, B, C)

assert not assoc.is_zero()
assert assoc.a == 0
assert assoc.u == e2
assert assoc.v == zero3
assert assoc.b == 0

# Determinant is split: diagonal signature has isotropic idempotents.
E_plus = Zorn(1, zero3, zero3, 0)
E_minus = Zorn(0, zero3, zero3, 1)
assert E_plus.det() == 0
assert E_minus.det() == 0

print("ZornAssociatorSplitOctonion.py: non-associative Zorn associator witness verified")
