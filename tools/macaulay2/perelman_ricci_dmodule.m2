-- tools/macaulay2/perelman_ricci_dmodule.m2
needsPackage "Dmodules"

-- We set up the Weyl algebra for n spatial dimensions and 1 time dimension.
-- Let's take n = 3: x, y, z, t.
W = QQ[x, y, z, t, dx, dy, dz, dt, WeylAlgebra => {
    x => dx,
    y => dy,
    z => dz,
    t => dt
}]

-- The heat equation operator P = dt - dx^2 - dy^2 - dz^2 (ignoring scaling factors)
P = dt - dx^2 - dy^2 - dz^2

-- The D-module M = W / <P>
I = ideal(P)

-- Compute the characteristic ideal (ideal of principal symbols)
CI = charIdeal I

-- Print the characteristic ideal
print("Characteristic Ideal:")
print(CI)

-- The characteristic variety is the zero set of charIdeal in the cotangent bundle.
-- Let's compute its dimension.
print("Dimension of the characteristic variety:")
print(dim CI)

if dim CI == 4 then (
    print("The D-module is holonomic.")
) else (
    print("The D-module is not holonomic.")
)
