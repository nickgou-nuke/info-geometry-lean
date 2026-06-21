needsPackage "Dmodules"

-- 1. Define the polynomial ring for the defect slice
R = QQ[x, y]

-- 2. Define the local Betti-8 defect polynomial
f = x^2 + y^2

-- 3. Compute the Bernstein-Sato polynomial (the global b-function)
bf = globalBFunction f
bfRoots = factorBFunction bf

print "=========================================================="
print "MACAULAY2 ALGEBRAIC DE RHAM MONODROMY CERTIFICATE"
print "=========================================================="
print "Polynomial f:"
print f
print "Bernstein-Sato polynomial (b-function):"
print bf
print "Factored roots of the b-function:"
print bfRoots
print "=========================================================="
print "The roots of this polynomial algebraically dictate the"
print "monodromy eigenvalues without needing complex analysis."
print "=========================================================="
