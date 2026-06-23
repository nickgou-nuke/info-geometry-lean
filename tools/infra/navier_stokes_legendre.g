# Navier-Stokes-Legendre theorem (GAP)
# Statement (informal):
#   L.fenchelGap(theta, eta) = 0  iff  Div( u ) = 0
# Placeholder: define a function that returns a string describing the theorem.

NavierStokesLegendreTheorem := function()
  return "Theorem: Fenchel-Legendre gap zero iff Madelung fluid divergence-free.";
end;

Print( NavierStokesLegendreTheorem(), "\n" );