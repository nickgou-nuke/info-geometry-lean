-- lasing_dmodule.m2
-- D-modules for the non-equilibrium metric flow driven by Itakura-Saito divergence
needsPackage "Dmodules"

W = QQ[x,y,t, dx, dy, dt, WeylAlgebra => {{x,dx}, {y,dy}, {t,dt}}]

-- Ideal representing the metric flow
I = ideal(x*dx + y*dy + t*dt, dx^2 + dy^2 - dt^2 + x*y)

-- Compute the Groebner basis
G = gb I

-- Check holonomicity
h = holonomicRank I

print "Lasing D-module constructed."
print "Holonomic rank (stability measure):"
print h
