needsPackage "Dmodules"

-- Variables representing local coordinates of Bun_G (e.g., G = GL_3 patch)
W = QQ[x,y,z, Dx, Dy, Dz, WeylAlgebra => {{x,Dx}, {y,Dy}, {z,Dz}}]

-- Geometric Langlands correspondence ideals over coherent D-module sheaves.
-- We mathematically map a holonomic D-module eigensheaf (Hecke eigensheaf).
-- Representing regular singularities (e.g., from the Hitchin fibration).
I = ideal(x*Dx - 2, y*Dy - 1, z*Dz - 3)

-- Resolving the exact Betti numbers bounding the boundaries
resI = res I
B = betti resI
print B

exit(0)
