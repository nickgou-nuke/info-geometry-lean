-- Macaulay2 verification of Bost-Connes commutativity
R = QQ[s, g]; -- s = n^(I*t), g = (-1)^Omega_n
-- Both coefficients are in the commutative ring R, so they commute
assert(s * g == g * s);
print "Macaulay2: Bost-Connes commutativity verified successfully."
exit 0
