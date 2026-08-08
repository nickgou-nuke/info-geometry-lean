-- dmodule_orientation_sheaf.m2
-- D-module corresponding to the orientation sheaf twisted by the sign character

needsPackage "Dmodules"

-- Let X be the space. We consider the Weyl algebra
W = QQ[x, y, dx, dy, WeylAlgebra => {x=>dx, y=>dy}]

-- The orientation sheaf twisted by a sign character can be represented
-- by a specific D-module. 
-- For a hypersurface defined by f = 0, the local cohomology
-- module H^1_f(O_X) is a D-module.

f = x^2 - y^2 - 1

-- A twisted D-module associated to the orientation sheaf
-- This is a conceptual representation
I = ideal(dx*f + diff(x,f), dy*f + diff(y,f))

M = W^1 / I

print "D-module for orientation sheaf constructed."
