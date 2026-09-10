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

# Actual spatial spinor current and the bounded-readout/unbounded-derivative family.
freq, xx, yy, kappa = S.symbols('freq xx yy kappa', real=True)
angle = freq * xx + S.pi / 4
spinor = S.Matrix([S.cos(angle), S.sin(angle) * S.exp(S.I * yy)])
rho = S.simplify((spinor.H * spinor)[0])
current_y = S.simplify(kappa * S.im((spinor.H * spinor.diff(yy))[0]))
assert rho == 1
assert S.simplify(current_y - kappa * S.sin(angle)**2) == 0
assert S.simplify(S.diff(current_y, xx).subs(xx, 0) - kappa * freq) == 0

# Three probes at the same vanishing-overlap family, including two non-poles
# of the real readout. The native Lean implementation guards epsilon=0.
epsilon = S.symbols('epsilon', real=True, nonzero=True)
pre, post = S.Matrix([1, 0]), S.Matrix([epsilon, 1])
denominator = (post.H * pre)[0]
sigma_x = S.Matrix([[0, 1], [1, 0]])
sigma_y = S.Matrix([[0, -S.I], [S.I, 0]])
weak_x = S.simplify((post.H * sigma_x * pre)[0] / denominator)
weak_y = S.simplify((post.H * sigma_y * pre)[0] / denominator)
weak_id = S.simplify((post.H * pre)[0] / denominator)
assert weak_x == 1 / epsilon
assert weak_y == S.I / epsilon and S.re(weak_y) == 0
assert weak_id == 1
success = epsilon**2 / (1 + epsilon**2)
assert S.simplify(success * weak_x**2 - 1/(1+epsilon**2)) == 0

# Both real quadratic forms are required to detect a complex zero overlap.
a, b, c, d = S.symbols('a b c d', real=True)
post_scalar, pre_scalar = a + S.I*b, c + S.I*d
z = S.Matrix([post_scalar, pre_scalar])
overlap = S.conjugate(post_scalar) * pre_scalar
assert S.simplify((z.H * sigma_x * z)[0] - 2*S.re(overlap)) == 0
assert S.simplify((z.H * sigma_y * z)[0] - 2*S.im(overlap)) == 0
assert sigma_x*sigma_y + sigma_y*sigma_x == S.zeros(2)

# Curvature squares survive the split algebra before flatness is imposed.
exterior, coderivative = S.symbols('exterior coderivative', commutative=False)
mixed = exterior*coderivative + coderivative*exterior
curvature = exterior**2 + coderivative**2
assert S.expand((exterior+coderivative)**2 - mixed - curvature) == 0
assert S.expand((exterior-coderivative)**2 + mixed - curvature) == 0
assert S.expand((exterior+coderivative)*(exterior-coderivative) +
                (exterior-coderivative)*(exterior+coderivative) -
                2*(exterior**2-coderivative**2)) == 0
print('PASS: spatial current, oscillation, guarded probe algebra, two overlap quadratics, curvature')
