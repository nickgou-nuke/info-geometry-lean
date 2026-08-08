-- ale_orbifold.m2
-- Define the Asymptotically Locally Euclidean (ALE) orbifold metric
-- as algebraic ideals and compute the D-module support.

R = QQ[x,y,z];

-- A1 singularity x^2 + y^2 + z^2 = 0 which is isomorphic to xy=z^2
I = ideal(x^2 + y^2 + z^2);

-- Jacobian matrix
J = jacobian I;

-- Singular locus ideal
SingLocus = I + ideal(J);

-- Support of the singularity
print "ALE Orbifold Ideal:"
print I

print "Singular Locus:"
print gens gb SingLocus
