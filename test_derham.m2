needsPackage "BernsteinSato"
needsPackage "Dmodules"

W = QQ[x, dx, WeylAlgebra=>{x=>dx}]
f = x^2
I_vars = ideal(dx)

print "Computing D-module localization..."
time M = Dlocalize(I_vars, f)

print "Computing algebraic de Rham cohomology via rationalFunctionExt..."
time dR = rationalFunctionExt(M)

print ("DLOCALIZE_EXT:result=" | toString(dR))
