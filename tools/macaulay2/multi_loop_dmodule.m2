needsPackage "Dmodules"
print "=== Macaulay2 Multi-Loop Logarithmic Score D-module ==="

W = QQ[x, y, Dx, Dy, WeylAlgebra => {x => Dx, y => Dy}]
use W

-- For a multi-loop integration or multi-parameter logarithmic score,
-- the functions often behave like log(x) + log(y) or log(x y).
-- Each independent log score component satisfies D_i (x_i D_i) = 0.
I = ideal(Dx * x * Dx, Dy * y * Dy)

print "Holonomic rank:"
r = holonomicRank(I)
print r

print "Characteristic variety:"
C = charIdeal(I)
print C

-- Ensure it's holonomic
assert(r == 4) -- since it's the product of two rank 2 D-modules

print "MULTI_LOOP_DMODULE_OK"
exit
