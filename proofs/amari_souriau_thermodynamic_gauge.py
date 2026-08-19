#!/usr/bin/env python3
"""
SymPy witness for the Amari--Souriau thermodynamic gauge deferred_interface.

Finite quadratic log-partition model:
    Ψ(θ) = 1/2 θᵀ A θ
with A symmetric positive definite.  Then
    η = ∇Ψ = A θ,
    g = Hess Ψ = A,
    D_Ψ(θ || θ*) = 1/2 (θ-θ*)ᵀ A (θ-θ*),
and the natural-gradient flow linearizes in dual coordinates:
    θdot = -A⁻¹ ∇D = -(θ-θ*)
    ηdot = A θdot = -(η-η*).

This is a symbolic witness only; Lean owns the theorem-safe deferred_interface.
"""
from sympy import Matrix, Rational, diff, simplify, symbols

# Symmetric positive-definite symbolic Hessian with determinant a*c-b^2.
a, b, c = symbols("a b c", positive=True)
th1, th2, st1, st2 = symbols("theta1 theta2 theta_star1 theta_star2")

A = Matrix([[a, b], [b, c]])
theta = Matrix([th1, th2])
theta_star = Matrix([st1, st2])

Psi = Rational(1, 2) * (theta.T * A * theta)[0]
grad = Matrix([diff(Psi, th1), diff(Psi, th2)])
hess = grad.jacobian(theta)
assert simplify(hess - A) == Matrix.zeros(2)
assert simplify(grad - A * theta) == Matrix.zeros(2, 1)

eta = grad
eta_star = A * theta_star
Delta = theta - theta_star
Bregman = simplify(
    Psi
    - Psi.subs({th1: st1, th2: st2})
    - ((A * theta_star).T * (theta - theta_star))[0]
)
assert simplify(Bregman - Rational(1, 2) * (Delta.T * A * Delta)[0]) == 0
assert simplify(Bregman.subs({th1: st1, th2: st2})) == 0

grad_D = Matrix([diff(Bregman, th1), diff(Bregman, th2)])
assert simplify(grad_D - A * Delta) == Matrix.zeros(2, 1)

theta_dot = simplify(-A.inv() * grad_D)
assert simplify(theta_dot + Delta) == Matrix.zeros(2, 1)

eta_dot = simplify(A * theta_dot)
assert simplify(eta_dot + (eta - eta_star)) == Matrix.zeros(2, 1)

# Exact one-form d log Q = dΨ is closed: dω = 0 in 2D.
omega1, omega2 = grad[0], grad[1]
exterior_derivative = simplify(diff(omega2, th1) - diff(omega1, th2))
assert exterior_derivative == 0

# Constant metric A and constant translation vector have zero Lie derivative.
X1, X2 = symbols("X1 X2")
X = Matrix([X1, X2])
lie_metric = Matrix([[0, 0], [0, 0]])
for i in range(2):
    for j in range(2):
        # X^k ∂_k g_ij + g_kj ∂_i X^k + g_ik ∂_j X^k ; all derivatives vanish.
        entry = sum(X[k] * diff(A[i, j], theta[k]) for k in range(2))
        entry += sum(A[k, j] * diff(X[k], theta[i]) for k in range(2))
        entry += sum(A[i, k] * diff(X[k], theta[j]) for k in range(2))
        lie_metric[i, j] = simplify(entry)
assert lie_metric == Matrix.zeros(2)

if __name__ == "__main__":
    print("Psi =", Psi)
    print("eta =", eta)
    print("Hessian =", hess)
    print("Bregman =", Bregman)
    print("theta_dot =", theta_dot)
    print("eta_dot =", eta_dot)
    print("d(d log Q) =", exterior_derivative)
    print("Lie_X g for constant X =", lie_metric)
