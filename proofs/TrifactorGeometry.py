import sympy as sp


# ─────────────────────────────────────────────────────────────────────────────
# Trifactor/Cubic projector algebra (scalar lane)
# ─────────────────────────────────────────────────────────────────────────────

op = sp.symbols("op")

# Spectral projectors in the OP root decomposition (for OP^3 = OP):
P_plus = sp.simplify(op * (op + 1) / 2)
P_minus = sp.simplify(op * (op - 1) / 2)
P_zero = sp.simplify(1 - op ** 2)


def cubic_factorization(expr: sp.Expr) -> sp.Expr:
    """Return OP^3 - OP as (OP-OP)(OP^2+... ), i.e. OP*(OP-1)*(OP+1)."""
    return sp.expand(expr ** 3 - expr)


# OP^3 = OP  <=>  OP*(OP-1)*(OP+1)=0
identity_cubic = cubic_factorization(op)
identity_factor = sp.expand(op * (op - 1) * (op + 1))
assert sp.expand(identity_cubic - identity_factor) == 0


def cubic_roots_from_factor(poly: sp.Expr):
    """Return symbolic root classes for OP^3-OP (real algebraic classes)."""
    f = sp.factor(poly)
    if f == sp.Integer(0):
        return [sp.Integer(-1), sp.Integer(0), sp.Integer(1)]
    return []


# Projector-sector reconstruction from cubic roots (formal check at the roots).

e_plus = sp.simplify(op * (op + 1) / 2)
e_minus = sp.simplify(op * (op - 1) / 2)
e_zero = sp.simplify(1 - op ** 2)

for root in [sp.Integer(-1), sp.Integer(0), sp.Integer(1)]:
    r = sp.Integer(root)
    assert e_plus.subs(op, r) ** 2 == e_plus.subs(op, r)
    assert e_minus.subs(op, r) ** 2 == e_minus.subs(op, r)
    assert e_zero.subs(op, r) ** 2 == e_zero.subs(op, r)
    assert e_plus.subs(op, r) + e_minus.subs(op, r) + e_zero.subs(op, r) == 1
    assert (P_plus.subs(op, r), P_minus.subs(op, r), P_zero.subs(op, r)) == (
        0 if r == -1 else (1 if r == 1 else 0),
        1 if r == -1 else (0 if r == 1 else 0),
        1 if r == 0 else 0,
    )

# Cubic classes realized as branches:
#  - OP = -1: minus projector branch
#  - OP = 0 : parabolic/null branch
#  - OP = 1 : plus projector branch
print("TrifactorGeometry.py: scalar cubic factorization and branch projector check passed")


# ─────────────────────────────────────────────────────────────────────────────
# 2x2 paravector/Pauli-style determinant lane
# ─────────────────────────────────────────────────────────────────────────────


def paravector_matrix(t, x, y, z):
    """Split Pauli-like 2x2 matrix; det = t^2 - x^2 - y^2 - z^2.

    Entries are complex-valued to encode two-vector directions via I.
    """
    return sp.Matrix(
        [
            [t + z, x - sp.I * y],
            [x + sp.I * y, t - z],
        ]
    )


def paravector_det(t, x, y, z):
    M = paravector_matrix(t, x, y, z)
    return sp.expand(M.det())


def paravector_q(t, x, y, z):
    return sp.expand(t ** 2 - x ** 2 - y ** 2 - z ** 2)


# symbolic identity
assert sp.expand(paravector_det(1, 2, 3, 4) - paravector_q(1, 2, 3, 4)) == 0


def lightcone_sector(t, x, y, z):
    q = paravector_q(t, x, y, z)
    return {
        "value": q,
        "sector": (
            "elliptic"
            if q.is_real and q.is_positive
            else "hyperbolic" if q.is_real and q.is_negative else "parabolic"
        ),
    }


# Example probes (kept symbolic-first / lightweight)
print("TrifactorGeometry.py: paravector det formula")
print("  det(matrix) = t^2 - x^2 - y^2 - z^2")
print("  sample", lightcone_sector(2, 1, 0, 0), lightcone_sector(1, 1, 0, 0))


# ─────────────────────────────────────────────────────────────────────────────
# Zorn-style null/paravector lane (symbolic)
# ─────────────────────────────────────────────────────────────


def vec(x, y, z):
    return sp.Matrix([x, y, z])


def dot(u, v):
    return sp.expand((u.T * v)[0])


def cross(u, v):
    return sp.Matrix(
        [
            sp.expand(u[1] * v[2] - u[2] * v[1]),
            sp.expand(u[2] * v[0] - u[0] * v[2]),
            sp.expand(u[0] * v[1] - u[1] * v[0]),
        ]
    )


class Zorn:
    """Zorn-type matrix [[a, u], [v, b]] with octonionic multiplication shell."""

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
        return all([sp.simplify(s) == 0 for s in [d.a, d.b] + list(d.u) + list(d.v)])

    def det(self):
        return sp.expand(self.a * self.b - dot(self.u, self.v))


zero3 = vec(0, 0, 0)

x, y, z = sp.symbols("x y z", commutative=True)
u = vec(x, y, z)

N_up = Zorn(0, u, zero3, 0)
N_down = Zorn(0, zero3, u, 0)

assert (N_up * N_up) == Zorn(0, zero3, zero3, 0)
assert (N_down * N_down) == Zorn(0, zero3, zero3, 0)
assert N_up.det() == 0
assert N_down.det() == 0

print("TrifactorGeometry.py: cubic projectors + paravector det + Zorn null lanes integrated")
