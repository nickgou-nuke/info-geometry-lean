"""Symbolic certificate for the 1+8+1 split TKK block model.

This mirrors SplitOctonionTKK55Blocks.lean:
  HIndex = minus | middle(0..7) | plus
  G55 = [[0, 0, 1], [0, eta44, 0], [1, 0, 0]]
  P(x), N(y), D(a,K)

The script verifies the orthogonality identities over a rational function
field. It is a derivation aid; Lean remains the formal authority.
"""
from sympy import Matrix, Rational, symbols, simplify, zeros

n = 8
sign = [1 if i < 4 else -1 for i in range(n)]
eta = diag = Matrix.diag(*sign)

G = zeros(n + 2)
G[0, n + 1] = 1
G[n + 1, 0] = 1
for i in range(n):
    G[i + 1, i + 1] = sign[i]

x = symbols("x0:8")
y = symbols("y0:8")
a = symbols("a")

flat_x = Matrix([sign[i] * x[i] for i in range(n)])
flat_y = Matrix([sign[i] * y[i] for i in range(n)])

P = zeros(n + 2)
for i in range(n):
    P[i + 1, 0] = x[i]
    P[n + 1, i + 1] = -flat_x[i]

N = zeros(n + 2)
for i in range(n):
    N[0, i + 1] = -flat_y[i]
    N[i + 1, n + 1] = y[i]

# Parameterize every eta-skew K by independent upper-triangular entries.
K = zeros(n)
for i in range(n):
    for j in range(i + 1, n):
        q = symbols(f"k{i}{j}")
        K[i, j] = q
        K[j, i] = -Rational(sign[i], sign[j]) * q

D = zeros(n + 2)
D[0, 0] = a
D[n + 1, n + 1] = -a
for i in range(n):
    for j in range(n):
        D[i + 1, j + 1] = K[i, j]

def zero_matrix(M):
    return all(simplify(v) == 0 for v in M)

def report(name, M):
    ok = zero_matrix(M)
    print(f"{name}: {'PASS' if ok else 'FAIL'}")
    if not ok:
        for i in range(M.rows):
            for j in range(M.cols):
                if simplify(M[i, j]) != 0:
                    print(f"  residual[{i},{j}] = {simplify(M[i,j])}")
    return ok

results = [
    report("P^T G + G P", P.T * G + G * P),
    report("N^T G + G N", N.T * G + G * N),
    report("D^T G + G D", D.T * G + G * D),
    report("eta^T - eta", eta.T - eta),
    report("eta^2 - I", eta * eta - Matrix.eye(n)),
]

# Verify the middle block constraint for the parameterization itself.
results.append(report("K^T eta + eta K", K.T * eta + eta * K))

if not all(results):
    raise SystemExit(1)
print("ALL_BLOCK_CERTIFICATES=PASS")
