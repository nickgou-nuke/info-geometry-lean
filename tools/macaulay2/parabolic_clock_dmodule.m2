-- Parabolic Clock D-module
-- Annihilator for the parabolic flow
-- M = I + t K
needsPackage "Dmodules"
A = QQ[t, Dt, WeylAlgebra => {t => Dt}]
use A

-- The flow is polynomial in t (degree 1)
-- So the D-module is annihilated by the second derivative Dt^2
I = ideal(Dt * Dt)
print "Holonomic rank of Parabolic Clock D-module (null vector flow):"
r = holonomicRank(I)
print r
assert(r == 2)

print "MACAULAY2_PARABOLIC_DMODULE_OK"
exit
