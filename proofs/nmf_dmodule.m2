-- Macaulay2 script for D-modules related to NMF and Itakura-Saito divergence
loadPackage "Dmodules"

-- We work over the Weyl algebra
n = 2; -- 2x2 case for simplicity
W = QQ[x11, x12, x21, x22, Dx11, Dx12, Dx21, Dx22, WeylAlgebra => {{x11, Dx11}, {x12, Dx12}, {x21, Dx21}, {x22, Dx22}}]

-- Itakura-Saito divergence: D_IS(X || Y) = sum(X_ij / Y_ij - log(X_ij / Y_ij) - 1)
-- We consider the differential operators annihilating the function exp(-D_IS(X || Y))
-- or simpler algebraic components.

-- Define operators for row sums and column sums
RowSum1 = x11*Dx11 + x12*Dx12
RowSum2 = x21*Dx21 + x22*Dx22
ColSum1 = x11*Dx11 + x21*Dx21
ColSum2 = x12*Dx12 + x22*Dx22

-- D-module for scaling invariance
I = ideal(RowSum1, RowSum2, ColSum1, ColSum2)

-- Gröbner basis in the Weyl algebra
G = gb I

print "Gröbner basis of the D-module ideal:"
print G

-- The holonomic rank
-- Use holonomicRank if available or just check dimension
print "Dimension:"
print dim(W/I)

exit
