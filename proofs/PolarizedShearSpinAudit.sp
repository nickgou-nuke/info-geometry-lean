"""Exact algebraic checks; Lean remains the proof authority."""
import sympy as S

A = S.Matrix([[1, 1], [0, 0]])
B = S.Matrix([[S.Rational(1, 2), 0], [S.Rational(1, 2), 0]])
P, Q = A * B, A * A
N = P * Q - Q * P
assert A * B * A == A and B * A * B == B
assert P.T == P and (B * A).T == B * A
assert A * A == A
assert N == S.Matrix([[0, 1], [0, 0]])
assert N * N == S.zeros(2)
assert P * N == N and N * P == S.zeros(2)
assert Q.T != Q
strain, rotation = (N + N.T) / 2, (N - N.T) / 2
assert strain * strain == -rotation * rotation
assert strain * rotation == -rotation * strain

s, w, nu = S.symbols('s w nu', real=True)
x0, x1 = S.symbols('x0 x1', real=True)
L = S.Matrix([[0, s + w], [s - w, 0]])
G = S.diag(w - s, w + s)
x = S.Matrix([x0, x1])
assert S.simplify(L * L - (s**2 - w**2) * S.eye(2)) == S.zeros(2)
assert S.simplify(L.T * G + G * L) == S.zeros(2)
damped = L - nu * S.eye(2)
assert S.simplify(damped.T * G + G * damped + 2 * nu * G) == S.zeros(2)
assert S.simplify((x.T * G * damped * x)[0] * 2 +
                  2 * nu * (x.T * G * x)[0]) == 0
print('PASS: nonzero MP/Drazin witness, Peirce corner, Clifford pair, weighted dissipation')
