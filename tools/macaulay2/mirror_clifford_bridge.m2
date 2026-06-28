-- Macaulay2 Verification: 3D Mirror Symmetry as Chiral Compass Swap
-- Algebraic Ideals of the Null Cones

print "=== Macaulay2: Mirror Clifford Bridge ==="

R = QQ[x0, x1, x2, x3, z, a]
-- Fraction field for q
F = fractionField(QQ[q])
S = R ** F

use S

-- Combined Null Cone Ideal
I_cone = ideal(x0^2 - x1^2 + x2^2 - x3^2)

-- Mirror Map Homomorphism
-- x0 -> x2, x1 -> x3, x2 -> x0, x3 -> x1
-- z -> a, a -> z
-- q -> q^-1
mirrorMap = map(S, S, {x2, x3, x0, x1, a, z})

-- Check ideal invariance
I_mirror = mirrorMap(I_cone)

if I_cone == I_mirror then
    print "  [PASS] Ideal of combined null cone is invariant under mirror swap"
else
    print "  [FAIL] Ideal not invariant"
end if

-- Applying mirror map twice returns the identity
-- Check generators
gens_original = matrix{{x0, x1, x2, x3, z, a}}
gens_swapped = mirrorMap(gens_original)
gens_double_swapped = mirrorMap(gens_swapped)

if gens_original == gens_double_swapped then
    print "  [PASS] Mirror map is an exact involution"
else
    print "  [FAIL] Mirror map is not an involution"
end if
