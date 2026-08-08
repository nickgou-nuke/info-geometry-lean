"""SymPy witness: three matrix-like encodings of octonions.

Checks the architectural point:
- ordinary matrices are associative, so they cannot faithfully represent octonions
  as an algebra under ordinary matrix multiplication;
- Zorn vector matrices encode split-octonions by changing multiplication;
- left-multiplication gives 8x8 linear operators, but L_x L_y != L_{xy};
- Cayley-Dickson pairs encode octonions by changing block multiplication.
"""

import sympy as sp

print("§1  Zorn vector-matrix multiplication is non-associative")

def dot(u, v):
    return sum(ui*vi for ui, vi in zip(u, v))

def cross(u, v):
    return [u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0]]

def zorn_mul(X, Y):
    a, u, v, b = X
    c, w, z, d = Y
    return (
        sp.simplify(a*c + dot(u, z)),
        [sp.simplify(a*w[i] + d*u[i] - cross(v, z)[i]) for i in range(3)],
        [sp.simplify(c*v[i] + b*z[i] + cross(u, w)[i]) for i in range(3)],
        sp.simplify(b*d + dot(v, w)),
    )

zero3 = [0, 0, 0]
e1, e2, e3 = [1,0,0], [0,1,0], [0,0,1]
X = (1, zero3, zero3, 0)
Y = (0, e1, zero3, 0)
Z = (0, e2, zero3, 0)
assoc_zorn = zorn_mul(zorn_mul(X, Y), Z)
assoc_zorn_rhs = zorn_mul(X, zorn_mul(Y, Z))
assert assoc_zorn != assoc_zorn_rhs
print("   (XY)Z != X(YZ) for Zorn multiplication ✓")

print("§2  Left multiplication is linear but not multiplicative")
# Use Cayley-Dickson octonions as R^8 tuples to build left multiplication matrices.
def qconj(q):
    return (q[0], -q[1], -q[2], -q[3])

def qmul(a, b):
    a0,a1,a2,a3 = a
    b0,b1,b2,b3 = b
    return (
        a0*b0 - a1*b1 - a2*b2 - a3*b3,
        a0*b1 + a1*b0 + a2*b3 - a3*b2,
        a0*b2 - a1*b3 + a2*b0 + a3*b1,
        a0*b3 + a1*b2 - a2*b1 + a3*b0,
    )

def omul(x, y):
    # Cayley-Dickson: (a,b)(c,d)=(ac - d*conj(b), conj(a)*d + c*b)
    a, b = x[:4], x[4:]
    c, d = y[:4], y[4:]
    first = tuple(sp.simplify(qmul(a,c)[i] - qmul(d, qconj(b))[i]) for i in range(4))
    second = tuple(sp.simplify(qmul(qconj(a), d)[i] + qmul(c,b)[i]) for i in range(4))
    return first + second

basis = [tuple(1 if i == j else 0 for i in range(8)) for j in range(8)]

def left_matrix(x):
    cols = [omul(x, e) for e in basis]
    return sp.Matrix.hstack(*[sp.Matrix(c) for c in cols])

x = basis[1]
y = basis[4]
Lx, Ly = left_matrix(x), left_matrix(y)
Lxy = left_matrix(omul(x,y))
assert Lx * Ly != Lxy
print("   L_x L_y != L_{xy}; left operators are linear, not an algebra representation ✓")

print("§3  Cayley-Dickson pairs are non-associative")
a, b, c = basis[1], basis[2], basis[4]
left = omul(omul(a,b), c)
right = omul(a, omul(b,c))
assert left != right
print("   Cayley-Dickson pair multiplication has nonzero associator ✓")

print("§4  Ordinary matrix multiplication remains associative")
A = sp.Matrix([[1,2],[3,4]])
B = sp.Matrix([[0,1],[-1,2]])
C = sp.Matrix([[2,0],[1,1]])
assert (A*B)*C == A*(B*C)
print("   standard matrix multiplication is associative, explaining the obstruction ✓")

print()
print("octonion_matrix_encodings.py: All identities verified")
