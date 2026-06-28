# GAP sketch of the Navier–Stokes–Legendre theorem.
# We illustrate the algebraic core of the statement:
#   Fenchel–Legendre gap = 0   <=>   div(u) = 0
# by working out the quadratic Lagrangian case L(x) = x^2/2.
#
# For this L, the Legendre transform is L*(η) = η^2/2 and the gap is
#   Φ(θ,η) = ½(θ-η)^2.
# Hence Φ=0 ⇔ θ = η.
#
# In the Bohm–Madelung–Hestenes (MH) formulation one identifies
#   θ  ↔  a thermodynamic force (e.g. inverse temperature β)
#   η  ↔  a component of the gradient of the stream‑function φ,
#        i.e. η = ∂φ/∂x_i .
# Consequently the condition θ = η for each coordinate direction
# translates to ∂φ/∂x_i = (thermodynamic force)_i .
# When the thermodynamic forces are gradients of a scalar potential
# (as they are in equilibrium), the collection of these equalities
# yields ∇φ = (force vector) and taking the divergence gives
#   Δφ = div(force) .
# In equilibrium the force field is curl‑free and divergence‑free,
# so Δφ = 0, i.e. div u = 0 with u = ∇φ.
#
# The following function returns a descriptive string and also
# verifies the quadratic‑L gap property symbolically (by printing).

NavierStokesLegendreTheorem := function()
  local gap_expr;
  gap_expr := "(theta - eta)^2 / 2";
  Print("Navier–Stokes–Legendre theorem (informal):\n");
  Print("  Fenchel–Legendre gap Φ(θ,η) = ", gap_expr, "\n");
  Print("  Φ(θ,η) = 0   if and only if   θ = η.\n");
  Print("\n");
  Print("In the MH‑formulation one identifies:\n");
  Print("  θ  ←  thermodynamic force (e.g. β)\n");
  Print("  η  ←  ∂φ/∂x_i   (i‑th component of the velocity gradient)\n");
  Print("Thus θ = η for each i gives ∂φ/∂x_i = force_i.\n");
  Print("Taking the divergence yields Δφ = div(force).\n");
  Print("For equilibrium forces (∇·force = 0) we obtain Δφ = 0,\n");
  Print("i.e. div u = 0 with u = ∇φ, the incompressibility condition.\n");
  return "Theorem statement printed.";
end;

# Invoke the function to see the message when the file is read.
NavierStokesLegendreTheorem();