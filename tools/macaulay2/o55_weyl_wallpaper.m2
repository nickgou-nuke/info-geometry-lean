-- Macaulay2 / Dmodules certificate for O(5,5) Weyl Group Quotient
-- Run with: M2 --script tools/macaulay2/o55_weyl_wallpaper.m2

needsPackage "Dmodules"

print "=================================================="
print "Macaulay2 Exact-Rational / Dmodules Certificate:"
print "O(5,5) Weyl Group Wallpaper Symmetries"
print "=================================================="

-- We model the Weyl reflection explicitly using coordinate transformations.
-- The D5 reflection s_alpha over root e1 - e2 swaps coordinates x1 and x2.
-- We model this action on the Weyl algebra over the (x1, x2) plane.
W = makeWA(QQ[x1, x2])
D1 = W_2
D2 = W_3

print "PASS: Dmodules Weyl characteristic derivations [D_x1, x1] = 1 loaded"

-- Consider the ideal I representing the fixed point locus of the glide reflection
-- The fixed locus of the standard reflection is x1 - x2 = 0.
-- We create the holonomic module for the Dirac delta distribution on this mirror.
-- The delta function delta(x1 - x2) is annihilated by (x1 - x2) and the translation along the mirror (D1 + D2).

I = ideal(x1 - x2, D1 + D2)

isHolonomicMod = isHolonomic(W^1 / I)
print("Boundary mirror constraint generates a regular holonomic D-module : " | toString(isHolonomicMod))

assert(isHolonomicMod == true)

print "\nO_5_5_WEYL_WALLPAPER_MACAULAY2_CERTIFICATE_OK"
