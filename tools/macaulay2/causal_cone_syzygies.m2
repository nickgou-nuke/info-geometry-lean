-- causal_cone_syzygies.m2
-- Model the left/right Rindler wedge algebra commutant intersection
-- and extract the exact syzygy modules for the dual polar singularity.

R = QQ[x,y,z,t]

-- Causal cone ideal
C = ideal(x^2 + y^2 + z^2 - t^2)

-- Left and Right Rindler wedge algebraic models (boundaries)
IL = ideal(x + t, y, z)
IR = ideal(x - t, y, z)

-- Commutant intersection
IIntersect = intersect(IL, IR)

-- Dual polar singularity ideal
-- The polar variety of a hypersurface f=0 is given by the ideal of partial derivatives
f = x^2 + y^2 + z^2 - t^2
JPolar = ideal(diff(x, f), diff(y, f), diff(z, f), diff(t, f)) + C

-- Syzygies for the commutant intersection
resIntersect = res IIntersect
bettiIntersect = betti resIntersect

-- Syzygies for the dual polar singularity
resPolar = res JPolar
bettiPolar = betti resPolar

print "=== Causal Cone ==="
print C

print "=== Commutant Intersection ==="
print IIntersect
print bettiIntersect

print "=== Dual Polar Singularity ==="
print JPolar
print bettiPolar

exit()
