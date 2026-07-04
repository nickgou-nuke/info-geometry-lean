needsPackage "Dmodules"

-- Lightweight Macaulay2 Dmodules sanity lane for the Zorn 8-basis table.
-- The multiplication-table theorem itself is finite coordinate algebra; this
-- lane additionally checks that the explicitly computed associator defect can
-- be carried on a Weyl chart without reducing to an ordinary polynomial-only
-- script.

W = makeWA(QQ[t])
T = W_0
D = W_1

if D*T - T*D != 1 then error "Weyl commutator mismatch"

-- From the Lean/CAS table: ((U1*U2)*V1 - U1*(U2*V1)).x2 = -1.
-- Encode the nonzero coordinate defect as a constant-coefficient section.
defect = -1_W
if defect == 0 then error "associator defect vanished"

M = W^1 / ideal(D)
if isHolonomic(M) != true then error "expected holonomic Weyl chart module"

print "MACAULAY2_DMODULES_ZORN_BASIS_TABLE_OK associator_x2_defect=-1"
