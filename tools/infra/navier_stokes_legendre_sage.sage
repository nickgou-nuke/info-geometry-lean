#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-
"""
SageMath sketch of the Navier–Stokes–Legendre theorem.

Mirrors the SymPy sketch but uses Sage's syntax.  The core idea is the
same: illustrate the equivalence between the vanishing Fenchel–Legendre
gap and the divergence‑free condition for a quadratic Lagrangian.
"""

# ----------------------------------------------------------------------
# 1.  Basic symbols
# ----------------------------------------------------------------------
# Thermodynamic / Legendre variables
theta, eta = var('theta eta', domain='real')

# Spatial coordinates (for the fluid picture)
X, Y = var('X Y', domain='real')

# ----------------------------------------------------------------------
# 2.  Quadratic Lagrangian L(x) = x^2/2  (so L(theta) = theta^2/2)
# ----------------------------------------------------------------------
# We'll compute the Fenchel–Legendre gap directly:
# Φ(θ,η) = L(θ) + L★(η) − θ·η
# For L(x)=x^2/2, the Legendre transform is L★(η)=η^2/2.
# Hence Φ(θ,η) = θ^2/2 + η^2/2 − θ·η = ½(θ−η)^2.
#
# We compute it symbolically:
L_theta = theta^2 / 2
L_star  = eta^2 / 2
Phi = L_theta + L_star - theta*eta
Phi_simplified = factor(Phi)  # should be 1/2*(theta - eta)^2

print("Fenchel‑Legendre gap (quadratic L):")
print(Phi_simplified)
print()
print("The gap vanishes iff  theta = eta :")
print(bool(Phi_simplified == 0))
print()

# ----------------------------------------------------------------------
# 3.  Fluid picture: velocity as gradient of a scalar potential
# ----------------------------------------------------------------------
# Let φ(X,Y) be a smooth scalar potential (stream‑function analogue)
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
# 4.  Statement of the (to‑be‑proved) equivalence
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
print("     (symbolic function) and keep the Legendre transform implicit.")
print("  2. Define the thermodynamic potentials (β, K, ω, …) as functions")
print("     of the same variables and identify θ, ν with appropriate")
print("     gradients of those potentials.")
print("  3. Show that, under the identification, the condition Φ=0")
print("     translates exactly to Δφ = 0, i.e. div u = 0.")
print("  4. Carry out the calculation in the chosen coordinate chart")
print("     (e.g. flat Euclidean space) and simplify with Sage.")