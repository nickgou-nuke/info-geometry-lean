
-- Experimental D-module de Rham audit for q(a) q(b) q(a-b) in C^8.
--
-- This is an intentionally heavy Macaulay2/Oaku computation.  It is not a Lean
-- certificate and should be launched through a timeout wrapper when possible.
-- A successful `rationalFunctionExt` table is evidence for the de Rham ranks;
-- a timeout or memory exhaustion is computational evidence only.

-- Load the packages containing Oaku/Takayama D-module algorithms.
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

print "DLOCALIZE_EXT:status=starting"
print "DLOCALIZE_EXT:model=q(a)*q(b)*q(a-b), dim=4, ambient_vars=8, weyl_vars=16"
print "DLOCALIZE_EXT:warning=heavy Oaku localization; run with an external timeout"

-- Localize the structure sheaf at the singularity f using Oaku's algorithm
time M = Dlocalize(I_vars, f)
print ("DLOCALIZE_EXT:localized_module_class=" | toString(class M))

print "DLOCALIZE_EXT:localization=completed"
print "DLOCALIZE_EXT:computing=rationalFunctionExt"
-- Ext groups compute algebraic de Rham data for the localized holonomic D-module.
time dRTable = rationalFunctionExt(M)

print ("DLOCALIZE_EXT:result=" | toString(dRTable))
