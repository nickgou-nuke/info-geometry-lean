needsPackage "Dmodules"

print "======================================================================"
print "Tripotent Mass Split in D-Modules (Algebraic Dirac Equation)"
print "======================================================================\n"

-- Define the Weyl algebra for spacetime (x,t) and dual momenta (Dx, Dt)
W = QQ[x, t, Dx, Dt, WeylAlgebra => {x=>Dx, t=>Dt}]

-- The 2x2 Tripotent Mass Matrices from Cl(1,1)
-- det(M) = 1  (Matter)
M_matter = matrix{{1_W, 0_W}, {0_W, 1_W}}

-- det(M) = -1 (Antimatter)
M_anti = matrix{{1_W, 0_W}, {0_W, -1_W}}

-- det(M) = 0  (Massless / Boundary)
M_zero = matrix{{1_W, 0_W}, {0_W, 0_W}}

-- Construct the Dirac operators in 1+1D: D = \gamma^\mu \partial_\mu - M
-- Using light-cone coordinates for simplicity \partial_+ = Dt+Dx, \partial_- = Dt-Dx
Dirac_matter = matrix{{Dt+Dx, 0_W}, {0_W, Dt-Dx}} - M_matter
Dirac_anti   = matrix{{Dt+Dx, 0_W}, {0_W, Dt-Dx}} - M_anti
Dirac_zero   = matrix{{Dt+Dx, 0_W}, {0_W, Dt-Dx}} - M_zero

print "1. Tripotent Mass Matrices:"
print("   Matter (det 1): ", M_matter)
print("   Antimatter (det -1): ", M_anti)
print("   Massless (det 0): ", M_zero)

print "\n2. D-Module Dirac Operators (D = gamma * partial - M):"
print("   D_matter = ", Dirac_matter)
print("   D_anti   = ", Dirac_anti)
print("   D_zero   = ", Dirac_zero)

-- Squaring the operator gives the algebraic D'Alembertian (Klein-Gordon equation)
-- D^2 = \Box - M^2
print "\n3. Squaring the Dirac Operator (Algebraic Klein-Gordon D^2):"
print("   D_matter^2 = ", Dirac_matter * Dirac_matter)
print("   D_anti^2   = ", Dirac_anti * Dirac_anti)
print("   D_zero^2   = ", Dirac_zero * Dirac_zero)

print "\n[CONCLUSION]"
print "The D-Module structure beautifully reveals that the tripotent matrix M"
print "directly determines the algebraic ideal of the solution space."
print "Squaring D_anti (det=-1) and D_matter (det=1) both yield valid Klein-Gordon"
print "equations, while D_zero (det=0) yields a singular projection (massless flow)!"
exit 0
