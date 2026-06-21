needsPackage "Dmodules"

-- Stage n (2D Thermodynamic Locus)
R1 = QQ[x, y]
Q1 = x^2 - y^2
-- The Jacobian ideal representing the critical singular locus
J1 = ideal(diff(x, Q1), diff(y, Q1))

-- Stage n+1 (4D Coordinate Shift / Embedding)
R2 = QQ[x, y, z, w]
Q2 = x^2 - y^2 + z^2 - w^2
J2 = ideal(diff(x, Q2), diff(y, Q2), diff(z, Q2), diff(w, Q2))

print "--- M2 SUPER-JACOBIAN TRANSFORMATION START ---"
print ("Dim of local critical locus J1: " | toString(dim(R1 / J1)))
print ("Dim of embedded critical locus J2: " | toString(dim(R2 / J2)))
print "--- M2 SUPER-JACOBIAN TRANSFORMATION END ---"
exit 0