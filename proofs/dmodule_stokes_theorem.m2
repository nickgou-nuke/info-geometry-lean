-- dmodule_stokes_theorem.m2
-- D-module mapping Stokes' theorem over path integrals

needsPackage "Dmodules"
R = QQ[x, y, dx, dy, WeylAlgebra => {{x, dx}, {y, dy}}]

-- Define a differential form analogue
-- omega = P dx + Q dy
P = x^2 * y
Q = x * y^2

-- Exterior derivative d(omega) = (dQ/dx - dP/dy) dx dy
d_omega = dx * Q - dy * P

-- Ideal representing the closed loop boundaries
I = ideal(x^2 + y^2 - 1)

print("D-module Stokes theorem formulation:")
print d_omega
