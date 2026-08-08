-- Metriplectic flow equations
-- Metriplectic dynamics combines Hamiltonian (symplectic) and dissipative (metric) dynamics.
-- dot{F} = {F, H} + [F, S]

R = QQ[x,y,z,p,q,r];

print "Metriplectic Flow System"
print "H = Hamiltonian (Energy), S = Entropy"
print "dot{x} = {x, H} + [x, S]"
print "Simulating flow equations..."
