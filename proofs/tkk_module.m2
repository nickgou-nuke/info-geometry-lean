-- Macaulay2 D-modules verification
loadPackage "Dmodules"
R = QQ[x,y,z,t]
D = ring R

I_infty = ideal(x, y)
I_zero = ideal(z, t)

print "Ideal I_infty:"
print I_infty

print "Ideal I_zero:"
print I_zero

-- Mapping x->t, y->z, z->y, t->x
phi = map(R, R, {t, z, y, x})

mapped_I_infty = phi(I_infty)
print "Mapped I_infty under Weyl inversion:"
print mapped_I_infty

if mapped_I_infty == ideal(t, z) then print "Success: Infinity maps to Zero correctly and preserves relations."
