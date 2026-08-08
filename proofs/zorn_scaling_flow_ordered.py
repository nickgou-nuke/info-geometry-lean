"""SymPy witness: Zorn scaling flow using tuple order (a,b,u,v).

This matches the user's snippet:
  X=(a,b,u,v), E=(p,1/p,0,0), E_inv=(1/p,p,0,0).

For Zorn multiplication in this order, conjugation gives:
  a -> a, b -> b, u -> p^2 u, v -> p^-2 v.
"""

import sympy as sp


def dot(x, y):
    return sum(xi * yi for xi, yi in zip(x, y))


def cross(x, y):
    return [
        x[1] * y[2] - x[2] * y[1],
        x[2] * y[0] - x[0] * y[2],
        x[0] * y[1] - x[1] * y[0],
    ]


def zorn_mul(X, Y):
    # tuple order: (a,b,u,v) representing [[a,u],[v,b]]
    a, b, u, v = X
    c, d, w, z = Y
    return (
        sp.simplify(a * c + dot(u, z)),
        sp.simplify(b * d + dot(v, w)),
        [sp.simplify(a * w[i] + d * u[i] - cross(v, z)[i]) for i in range(3)],
        [sp.simplify(c * v[i] + b * z[i] + cross(u, w)[i]) for i in range(3)],
    )


p = sp.symbols("p", positive=True)
a, b = sp.symbols("a b", real=True)
u = [sp.symbols(f"u{i}", real=True) for i in range(3)]
v = [sp.symbols(f"v{i}", real=True) for i in range(3)]

X = (a, b, u, v)
E = (p, 1 / p, [0, 0, 0], [0, 0, 0])
E_inv = (1 / p, p, [0, 0, 0], [0, 0, 0])

EX = zorn_mul(E, X)
EX_Einv = zorn_mul(EX, E_inv)

print("EX_Einv top-left:", sp.simplify(EX_Einv[0]))
print("EX_Einv bottom-right:", sp.simplify(EX_Einv[1]))
print("EX_Einv top-right:", [sp.simplify(x) for x in EX_Einv[2]])
print("EX_Einv bottom-left:", [sp.simplify(x) for x in EX_Einv[3]])

assert sp.simplify(EX_Einv[0] - a) == 0
assert sp.simplify(EX_Einv[1] - b) == 0
assert all(sp.simplify(EX_Einv[2][i] - p**2 * u[i]) == 0 for i in range(3))
assert all(sp.simplify(EX_Einv[3][i] - v[i] / p**2) == 0 for i in range(3))

Upper = (0, 0, u, [0, 0, 0])
Lower = (0, 0, [0, 0, 0], v)
Zero = (0, 0, [0, 0, 0], [0, 0, 0])
assert zorn_mul(Upper, Upper) == Zero
assert zorn_mul(Lower, Lower) == Zero

print("zorn_scaling_flow_ordered.py: All identities verified")
