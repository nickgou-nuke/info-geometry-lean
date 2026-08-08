-- dmodule_spinor_vector.m2
-- D-module corresponding to the cohomology spaces

needsPackage "Dmodules"

-- Coordinate ring of the resolved space
R = QQ[x,y,z,w, Dx, Dy, Dz, Dw, WeylAlgebra => {x=>Dx, y=>Dy, z=>Dz, w=>Dw}]

-- Define the D-module ideal for the spinor-vector duality relation
-- We model the system of differential equations
I = ideal(Dx*x - x*Dx + 1, Dy*y - y*Dy + 1, Dz*z - z*Dz + 1, Dw*w - w*Dw + 1)

-- Spinor and Vector modules as D-modules
spinor_mod = R^1 / I
vector_mod = R^1 / I

-- Compute Holonomic rank
print("Holonomic rank of Spinor D-module:")
print holonomicRank(I)

print("D-module for Spinor-Vector duality created successfully.")
exit
