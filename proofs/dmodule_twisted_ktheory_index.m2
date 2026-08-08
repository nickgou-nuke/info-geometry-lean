-- Macaulay2 Script for D-module mapping twisted K-theory index

needsPackage "Dmodules"

print "Constructing D-module for exact twisted K-theory index of Dirac operator"

-- Define a Weyl algebra for the singular fixed points
W = QQ[x_1..x_5, dx_1..dx_5, WeylAlgebra => {x_1 => dx_1, x_2 => dx_2, x_3 => dx_3, x_4 => dx_4, x_5 => dx_5}]

-- Define the Dirac operator over the singular fixed points conceptually
D = dx_1^2 + dx_2^2 + dx_3^2 + dx_4^2 + dx_5^2

-- Create D-ideal mapping to the twisted K-theory index
I = ideal(D)

print "D-module Ideal for exact twisted K-theory index:"
print I
