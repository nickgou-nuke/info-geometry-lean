-- pin55_root_space.m2
-- D-module corresponding to the Root Space Decomposition of the Pin(5,5) algebra.

needsPackage "Dmodules"

print "Constructing the D-module corresponding to the Root Space Decomposition of the Pin(5,5) algebra..."

-- Create a Weyl algebra for the Cartan subalgebra and root spaces of D5
-- The Cartan subalgebra has dimension 5.
WA = QQ[x_1..x_5, dx_1..dx_5, WeylAlgebra => {x_1=>dx_1, x_2=>dx_2, x_3=>dx_3, x_4=>dx_4, x_5=>dx_5}]

-- Define a D-module ideal corresponding to the root system (simplified example)
I = ideal(dx_1^2 + dx_2^2 + dx_3^2 + dx_4^2 + dx_5^2)
Dmod = WA / I

print "D-module successfully constructed."
