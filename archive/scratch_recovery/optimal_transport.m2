-- Auto-generated Spinor Prima Materia System
loadPackage "Dmodules"
-- Ambient Supergraded Ring Setup
W = RR_53[x, D, theta, SkewCommutative => {theta}]

-- Bogoliubov mixing coefficients
coshVal = 1.257767
sinhVal = 0.762874

-- Supergraded generating potential under Unruh deformation
-- Combines bosonic (x, D) and fermionic (theta) sectors
superPotential = (coshVal^2 + sinhVal^2)*(x*D + theta) + 2*coshVal*sinhVal*(x*theta)

-- Compute the Super-Hessian Gradient Flow Locus
gradientIdeal = ideal(jacobian(matrix{{superPotential}}))

-- Extract fixed point dimension
print(toString(dim(gradientIdeal)))
exit 0
