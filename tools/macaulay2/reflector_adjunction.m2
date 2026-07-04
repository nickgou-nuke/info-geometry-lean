-- reflector_adjunction.m2
R = QQ[x, y, z]
M = R^3
N = image matrix{{x, y, 0}, {0, x, y}, {z, 0, x}}
Q = cokernel matrix{{x, y, 0}, {0, x, y}, {z, 0, x}}

print betti Q

resQ = res Q
print betti resQ

H = Hom(Q, Q)
print H

exit
