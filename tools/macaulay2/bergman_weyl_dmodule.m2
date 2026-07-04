needsPackage "Dmodules"

-- The Bergman Kernel potential Phi = log(B(z, w))
-- We model this in the Weyl algebra QQ<z, w, Dz, Dw> where w is zbar
W = QQ[z, w, Dz, Dw, WeylAlgebra => {z=>Dz, w=>Dw}]

-- The Kähler metric is omega = dz ^ dw \partial_z \partial_w Phi
-- We construct a D-module corresponding to the mixed derivative operator Dz * Dw
L = ideal(Dz * Dw)

-- Compute the Groebner basis
G = gb(L)
print "=== Groebner basis of the Bergman metric operator ideal ==="
print G

-- The holonomic rank calculates the dimension of the solution space
print "=== Holonomic rank of the Bergman metric module ==="
print holonomicRank(L)

-- Multi-loop Extension: Dz^2 Dw^2
Lmulti = ideal(Dz^2 * Dw^2)
print "=== Holonomic rank of the 2-loop extended operator ideal ==="
print holonomicRank(Lmulti)

-- Evaluate the operator on a symbolic representation
-- We can also check the commutation relations to verify Weyl algebra setup
print "=== Weyl Commutation Relation (Dz * z - z * Dz) ==="
print (Dz * z - z * Dz)
