#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-
"""
SageMath sketch of the Navier–Stokes–Legendre theorem.

Mirrors the SymPy sketch but uses Sage's syntax.  The core idea is the
same: illustrate the structure of the statement
    Fenchel–Legendre gap = 0   <=>   div( u ) = 0
by working out a concrete quadratic Lagrangian example and indicating
how the general case would proceed.
"""

# ----------------------------------------------------------------------
# 1.  Basic symbols (using Sage's symbolic ring)
# ----------------------------------------------------------------------
theta, eta = var('theta eta', domain='RR')
x = var('x', domain='RR')
X, Y = var('X Y', domain='RR')

# ----------------------------------------------------------------------
# 2.  A concrete convex Lagrangian L(x)
# ----------------------------------------------------------------------
L = x^2 / 2          # L : R -> R,  L'(x) = x

# ----------------------------------------------------------------------
# 3.  Legendre‑Fenchel transform L★(η)
# ----------------------------------------------------------------------
# Solve L'(x) = eta  for x  (here: x = eta)
x_star = solve(diff(L, x) - eta, x)[0]   # => eta
L_star = simplify(x_star * eta - L.subs(x, x_star))
# L_star = eta^2 / 2

# ----------------------------------------------------------------------
# 4.  Fenchel‑Legendre gap
# ----------------------------------------------------------------------
Phi = L + L_star - theta * eta
Phi_simplified = simplify(Phi.subs({L: x^2/2, L_star: eta^2/2}))
Phi_simplified = simplify(Phi_simplified.subs(x, eta))
# Result: Phi = 1/2 * (theta - eta)^2
Phi_simplified = simplify(Phi_simplified)

print("Fenchel‑Legendre gap (quadratic L):")
print(Phi_simplified)
print()
print("The gap vanishes iff  theta = eta :")
print(bool(Phi_simplified == 0))
print()

# ----------------------------------------------------------------------
# 5.  Fluid picture: velocity as gradient of a scalar potential
# ----------------------------------------------------------------------
# Let φ(X,Y) be a smooth scalar potential (function)
phi = function('phi')(X, Y)

# Velocity field u = (u_x, u_y) = grad φ
u_x = diff(phi, X)
u_y = diff(phi, Y)

# Divergence of u: div u = ∂_X u_x + ∂_Y u_y = Δφ (Laplacian)
div_u = diff(u_x, X) + diff(u_y, Y)

print("Velocity components (u_x, u_y):")
print((u_x, u_y))
print()
print("Divergence of u (i.e. Δφ):")
print(div_u)
print()

# ----------------------------------------------------------------------
# 6.  Statement of the (to‑be‑proved) equivalence
# ----------------------------------------------------------------------
print("=== To be proved (placeholder) ===")
print("Theorem (informal):")
print("    Fenchel‑Legendre gap Φ(θ,η) = 0   ⇔   div( u ) = 0")
print("where")
print("    Φ(θ,η) = L(θ) + L★(η) − ⟨θ,η⟩")
print("    u      = ∇φ   (velocity from a scalar potential)")
print("    div u  = Δφ   (Laplacian of the potential)")
print()
print("For the quadratic L = x²/2 the left‑hand side reduces to ½(θ−η)²,")
print("so Φ=0 ⇔ θ = η.  Matching θ with a thermodynamic force and η with")
print("a component of ∇φ yields the infinitesimal version of the")
print("divergence‑free condition once all spatial directions are accounted for.")
print()
print("Next steps:")
print("  1. Replace the quadratic L by an unspecified convex function")
print("     (sage.symbolic.function.Function) and keep the Legendre transform implicit.")
print("  2. Define the thermodynamic potentials (β, K, ω, …) as functions")
print("     of the same variables and identify θ, η with appropriate")
print("     gradients of those potentials.")
print("  3. Show that, under the identification, the condition Φ=0")
print("     translates exactly to Δφ = 0, i.e. div u = 0.")
print("  4. Carry out the calculation in the chosen coordinate chart")
print("     (e.g. flat Euclidean space) and simplify with Sage.")