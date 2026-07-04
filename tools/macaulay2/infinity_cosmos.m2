needsPackage "SimplicialComplexes"

-- Define base ring
R = QQ[x,y,z,w]

-- Define a simplicial complex: cycle of 4 edges (boundary of a square)
D = simplicialComplex {x*y, y*z, z*w, w*x}

-- 1. Simplicial algebraic invariants
I_D = ideal D

print "=== Simplicial Complex Ideal ==="
print I_D

print "=== Reduced Homology ==="
H = homology D
print H

-- Get the free resolution of R^1/I_D
M = R^1 / I_D
C = res M

print "=== Free Resolution ==="
print C

print "=== Betti Numbers ==="
print betti C

-- 2. Verify the homology boundaries natively
d1 = C.dd_1
d2 = C.dd_2
d3 = C.dd_3

print "=== Verifying Homology Boundaries Natively ==="
print "d1 * d2 == 0:"
print( d1 * d2 == 0 )
print "d2 * d3 == 0:"
print( d2 * d3 == 0 )

-- 3. Enriched change-of-base functors
-- We do a change of base to another module N
I_base = ideal(x-y, z-w)
N = R^1 / I_base

print "=== Enriched Change-of-Base Functors ==="

-- Tor_1(M, N)
T1 = Tor_1(M, N)
print "Tor_1(M, N):"
print T1

-- Ext^1(M, N)
E1 = Ext^1(M, N)
print "Ext^1(M, N):"
print E1

exit(0)
