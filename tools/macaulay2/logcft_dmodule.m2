needsPackage "Dmodules"
print "=== Macaulay2 LogCFT D-module ==="

W = QQ[x, Dx, WeylAlgebra => {x => Dx}]
use W

-- The logarithm f(x) = log(x) satisfies x * f'(x) = 1
-- Taking another derivative: D_x (x D_x f) = 0
-- So the D-module is annihilated by Dx * (x * Dx)
-- In Weyl algebra, Dx * x = x * Dx + 1, so Dx * x * Dx = x * Dx^2 + Dx
I = ideal(Dx * x * Dx)

print "Holonomic rank of log(x) D-module:"
r = holonomicRank(I)
print r
assert(r == 2)
print "MACAULAY2_LOGCFT_OK"
exit
