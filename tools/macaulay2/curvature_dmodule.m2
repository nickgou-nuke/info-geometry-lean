needsPackage "Dmodules"

-- D-module for the non-Abelian gauge connection (SU(2) flat connection)
-- A connection on a trivial bundle over A^3
W = QQ[x,y,z, Dx,Dy,Dz, WeylAlgebra=>{x=>Dx, y=>Dy, z=>Dz}]

-- Flat connection derived from pure gauge g = matrix{{1, x}, {y, 1+x*y}}
Ax = matrix{{0, 1}, {0, 0}}
Ay = matrix{{-x, -x^2}, {1, x}}
Az = matrix{{0, 0}, {0, 0}}

id2 = matrix{{1_W, 0}, {0, 1_W}}

-- The covariant derivatives act on the basis sections. The D-module relations are given by:
-- nabla_i = D_i * id + A_i^T
nablaX = Dx * id2 + transpose(Ax)
nablaY = Dy * id2 + transpose(Ay)
nablaZ = Dz * id2 + transpose(Az)

-- The D-module is defined as the cokernel of the relations matrix
myGens = nablaX | nablaY | nablaZ
Dmod = cokernel myGens

print("Checking holonomicity of the non-Abelian gauge connection D-module...")
d = dim(Dmod)
h = holonomicRank(Dmod)
print("Dimension of the D-module: " | toString d)
print("Holonomic rank of the connection: " | toString h)

if d == 3 then (
    print("The D-module is holonomic, verifying it is a flat connection.");
) else (
    print("The D-module is NOT holonomic.");
    exit 1;
)

exit 0
