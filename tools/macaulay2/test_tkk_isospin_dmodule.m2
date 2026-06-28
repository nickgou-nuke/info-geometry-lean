-- test_tkk_isospin_dmodule.m2
-- Formalization of the TKK Isospin system using D-modules

needsPackage "Dmodules"

-- 1. Defines the Weyl algebra corresponding to the TKK coordinates.
-- We use u, v for the internal SU(2) isospin coordinates
-- and x, y for space-time/TKK Jordan algebra coordinates.
W = QQ[x, y, u, v, dx, dy, du, dv, WeylAlgebra => {x=>dx, y=>dy, u=>du, v=>dv}]

-- 2. Defines the SU(2) generators as differential operators.
Jp = u*dv
Jm = v*du
Jz = 1/2*(u*du - v*dv)

-- 4a. Verify the embedding of SU(2) inside the structure derivation algebra.
-- The generators must satisfy the standard su(2) commutation relations.
c1 = Jp*Jm - Jm*Jp - 2*Jz
c2 = Jz*Jp - Jp*Jz - Jp
c3 = Jz*Jm - Jm*Jz + Jm

is_su2 = (c1 == 0 and c2 == 0 and c3 == 0)

if is_su2 then (
    print "SU(2) embedding into derivation algebra: VERIFIED"
) else (
    print "SU(2) embedding into derivation algebra: FAILED"
)

-- 3. Constructs the D-module ideal representing the TKK states.
-- The TKK grading operator (Euler operator on Jordan coordinates)
E_TKK = x*dx + y*dy
-- The isospin grading operator
E_iso = u*du + v*dv

-- Ideal for a specific state: TKK degree 1, Isospin highest weight state of spin 1/2
-- Thus: E_TKK - 1 = 0, E_iso - 1 = 0, Jp = 0, Jz - 1/2 = 0
-- To avoid fractions in the ideal generators over QQ, we clear denominators: 2*Jz - 1 = 0
I_TKK = ideal(E_TKK - 1, E_iso - 1, Jp, 2*Jz - 1)

M_TKK = W^1 / I_TKK

-- 4b. Computes the dimension.
-- Compute the Krull dimension of the D-module.
-- W has 4 variables, so the dimension of the Weyl algebra is 8.
-- A holonomic D-module will have dimension 4.
d = dim M_TKK

print ("D-module Dimension: " | toString(d))

-- Final verdict
if is_su2 and d > 0 then (
    print "PASS"
) else (
    print "FAIL"
)
exit(0)
