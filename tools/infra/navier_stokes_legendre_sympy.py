#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SymPy sketch of the Navier–Stokes–Legendre theorem.

We illustrate the *structure* of the statement:
    Fenchel–Legendre gap = 0   <=>   div( u ) = 0

where
    • the gap comes from a Legendre transform of a convex Lagrangian L,
    • the velocity field u is obtained as the gradient of a scalar potential φ,
    • divergence‑freeness is the vanishing Laplacian of φ.

For a *quadratic* L the equivalence can be checked symbolically;
the general case is left as future work (the same scaffolding works
with an unspecified sympy.Function).
"""

import sympy as sp

# ----------------------------------------------------------------------
# 1.  Basic symbols
# ----------------------------------------------------------------------
# Thermodynamic / Legendre variables
theta, eta = sp.symbols('theta eta', real=True)
# Auxiliary variable for the Legendre transform (the "state" variable)
x = sp.symbols('x', real=True)

# Spatial coordinates (for the fluid picture)
X, Y = sp.symbols('X Y', real=True)

# ----------------------------------------------------------------------
# 2.  A concrete convex Lagrangian L(x)
# ----------------------------------------------------------------------
# Choose a simple strictly convex function so that the Legendre transform
# is available in closed form.  In a full development L would be an
# arbitrary smooth convex function (perhaps coming from a thermodynamic
# potential).
L_expr = x**2 / 2          # L : R -> R,  L'(x) = x

# ----------------------------------------------------------------------
# 3.  Legendre‑Fenchel transform L★(η)
# ----------------------------------------------------------------------
# Solve  L'(x) = eta  for x  (here: x = eta)
x_star = sp.solve(sp.diff(L_expr, x) - eta, x)[0]   # => eta
L_star = sp.simplify(x_star * eta - L_expr.subs(x, x_star))
# L_star = eta**2 / 2

# ----------------------------------------------------------------------
# 4.  Fenchel‑Legendre gap: Φ(θ,η) = L(θ) + L★(η) − ⟨θ,η⟩
# ----------------------------------------------------------------------
L_theta = L_expr.subs(x, theta)   # L(θ) = θ²/2
Phi = L_theta + L_star - theta * eta
# Substitute L_star
Phi_simplified = sp.simplify(Phi.subs(L_star, eta**2/2))
# Now Phi = θ²/2 + η²/2 − θ·η
Phi_simplified = sp.simplify(Phi_simplified)
# Which equals ½(θ−η)²
Phi_simplified = sp.factor(Phi_simplified)

print("Fenchel‑Legendre gap (quadratic L):")
sp.pprint(Phi_simplified)
print()
print("The gap vanishes iff  theta = eta :")
print(sp.simplify(Phi_simplified) == 0)
print()

# ----------------------------------------------------------------------
# 5.  Fluid picture: velocity as gradient of a scalar potential
# ----------------------------------------------------------------------
# Let φ(X,Y) be a smooth scalar potential (stream‑function analogue)
phi = sp.Function('phi')(X, Y)

# Velocity field u = (u_x, u_y) = grad φ
u_x = sp.diff(phi, X)
u_y = sp.diff(phi, Y)

# Divergence of u: div u = ∂_X u_x + ∂_Y u_y = Δφ (Laplacian)
div_u = sp.diff(u_x, X) + sp.diff(u_y, Y)

print("Velocity components (u_x, u_y):")
sp.pprint((u_x, u_y))
print()
print("Divergence of u (i.e. Δφ):")
sp.pprint(div_u)
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
print("     (sympy.Function) and keep the Legendre transform implicit.")
print("  2. Define the thermodynamic potentials (β, K, ω, …) as functions")
print("     of the same variables and identify θ, ν with appropriate")
print("     gradients of those potentials.")
print("  3. Show that, under the identification, the condition Φ=0")
print("     translates exactly to Δφ = 0, i.e. div u = 0.")
print("  4. Carry out the calculation in the chosen coordinate chart")
print("     (e.g. flat Euclidean space) and simplify with sympy.")