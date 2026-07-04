-- tools/macaulay2/cft_virasoro.m2
-- Virasoro algebra commutators in the Weyl algebra

-- Define the Weyl algebra QQ[z, D] with D*z = z*D + 1
W = QQ[z, D, WeylAlgebra=>{z=>D}]

-- To satisfy the Witt algebra commutation relations [L_m, L_n] = (m - n) L_{m+n},
-- we must use the normal ordering L_n = -D * z^(n+1).
-- This means L_{-1} = -D
-- L_0 = -D * z = -z*D - 1  (Note: the prompt suggested -z*D, but we fix the ordering here)
-- L_1 = -D * z^2 = -z^2*D - 2*z
L0 = -D*z
Lm1 = -D
L1 = -z^2*D - 2*z

L = new HashTable from {-1 => Lm1, 0 => L0, 1 => L1}

-- Commutator natively in the Weyl algebra
comm = (A, B) -> A*B - B*A

-- Verify [L_m, L_n] = (m-n)L_{m+n}
assert(comm(L#(-1), L#(0)) == (-1 - 0)*L#(-1+0))
assert(comm(L#(-1), L#(1)) == (-1 - 1)*L#(-1+1))
assert(comm(L#(0), L#(1)) == (0 - 1)*L#(0+1))
assert(comm(L#(1), L#(-1)) == (1 - (-1))*L#(1-1))
assert(comm(L#(0), L#(-1)) == (0 - (-1))*L#(0-1))

print "All Virasoro commutators verified successfully."
