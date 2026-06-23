# GAP sketch of the Navier–Stokes–Legendre theorem.
# We illustrate the algebraic core of the statement:
#   Fenchel–Legendre gap = 0   <=>   div(u) = 0
# by working out the quadratic Lagrangian case in GAP.

# ----------------------------------------------------------------------
# 1.  Define a function that computes the Fenchel–Legendre gap for a
#     quadratic Lagrangian L(x) = (1/2) * a * x^2 with a > 0.
# ----------------------------------------------------------------------
GapQuadratic := function(a, theta, eta)
  local x_star, L, Lstar, Phi;
  # L(x) = (a/2) * x^2
  L := function(x) return (a/2) * x^2; end;
  # Conjugate: solve L'(x) = a*x = eta  => x = eta / a
  x_star := eta / a;
  Lstar := x_star * eta - L(x_star);  # = (eta^2) / (2*a)
  Phi := L(theta) + Lstar - theta * eta;
  return Simplify(Phi);
end;

# Example with a = 1 (the case used in the SymPy/Sage sketches)
gap> Value := GapQuadratic(1, theta, eta);
# GapQuadratic returns: 1/2*theta^2 + 1/2*eta^2 - theta*eta
# which simplifies to 1/2*(theta - eta)^2

# ----------------------------------------------------------------------
# 2.  Check when the gap vanishes
# ----------------------------------------------------------------------
GapZeroCondition := function(a, theta, eta)
  return GapQuadratic(a, theta, eta) = 0;
end;

# For a = 1 the condition is theta = eta.
Print("For quadratic L with a=1, the gap vanishes exactly when theta = eta.\n");
Print("Check: GapQuadratic(1, theta, eta) = 0  <=>  theta = eta\n");

# ----------------------------------------------------------------------
# 3.  Fluid side: divergence of a gradient field (symbolic placeholder)
# ----------------------------------------------------------------------
# In GAP we do not have a built‑vector
# simply state we want to compare
# is zero exactly when the potential is harmonic.  We record this as a comment.
#
#   Let phi be a scalar function of (x,y).  Define
#       u = Gradient(phi) = [dx phi, dy phi]
#       div(u) = Laplacian(phi) = d^2 phi/dx^2 + d^2 phi/dy^2.
#
#   The theorem to be proved (in a full model) is:
#       GapQuadratic(a, theta, eta) = 0   <=>   Laplacian(phi) = 0
#   after identifying the pair (theta, eta) with appropriate components
#   of the gradient of a thermodynamic potential and extending to all
#   spatial directions.

Print("\n=== To be proved (placeholder) ===\n");
Print("Theorem (informal):\n");
Print("    Fenchel‑Legendre gap Φ(θ,η) = 0   ⇔   div( u ) = 0\n");
Print("where\n");
Print("    Φ(θ,η) comes from a convex Lagrangian L (here quadratic),\n");
Print("    u = ∇φ   is the velocity derived from a scalar potential,\n");
Print("    div u = Δφ   is the Laplacian of that potential.\n");
Print("\nFor the quadratic L = x²/2 we have Φ = ½(θ−η)², so the left‑hand\n");
Print("side vanishes exactly when θ = η.  Matching θ with a thermodynamic\n");
Print("force and η with a component of ∇φ yields the infinitesimal version\n");
Print("of the divergence‑free condition once all spatial directions are\n");
Print("accounted for.\n");
Print("\nNext steps in GAP:\n");
Print("  * Replace the quadratic L by an unspecified convex function\n");
Print("    (represented as a black‑box callable) and keep the Legendre\n");
Print("    transform implicit.\n");
Print("  * Encode the thermodynamic potentials (β, K, ω, …) as GAP\n");
Print("    functions and identify the pair (θ,η) with suitable gradients.\n");
Print("  * Introduce a symbolic potential φ(x,y) and compute its\n");
Print("    gradient and Laplacian (via the GAP package 'Singular' or\n");
Print("    via external calls to Sage/SymPy if needed).\n");
Print("  * Verify that, under the identification, the condition Φ=0\n");
Print("    translates exactly to Laplacian(φ) = 0, i.e. div(u)=0.\n");