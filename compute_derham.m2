
-- Load the BernsteinSato package which contains the Oaku algorithms for D-modules
needsPackage "BernsteinSato"
needsPackage "Dmodules"

-- Define the polynomial ring in 8 variables with their Weyl differentials
W = QQ[a1,a2,a3,a4, b1,b2,b3,b4, da1,da2,da3,da4, db1,db2,db3,db4, WeylAlgebra => {
    a1 => da1, a2 => da2, a3 => da3, a4 => da4,
    b1 => db1, b2 => db2, b3 => db3, b4 => db4
}]

-- Define the quadrics for D=4
qa = a1^2 + a2^2 + a3^2 + a4^2
qb = b1^2 + b2^2 + b3^2 + b4^2
qab = (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2 + (a4-b4)^2

-- Define the singular hypersurface polynomial f
f = qa * qb * qab

-- The base structure sheaf ideal D-module for C^8
I_vars = ideal(da1,da2,da3,da4, db1,db2,db3,db4)

print "---"
print "WARNING: Initiating Weyl algebra localization O(*V(f)) for 8-variables, degree 6."
print "This will compute the b-function and its roots, requiring Grobner basis in 16 variables."
print "This operation is deeply exponential and may exceed all available RAM/Time."
print "---"

-- Localize the structure sheaf at the singularity f using Oaku's algorithm
time M = Dlocalize(I_vars, f)

print "Localization completed! Computing Ext for algebraic de Rham Betti numbers..."
-- Ext groups compute the algebraic de Rham cohomology for localized holonomic D-modules
time b_numbers = rationalFunctionExt(M)

print "The algebraic de Rham Betti numbers of the complement are:"
print b_numbers
