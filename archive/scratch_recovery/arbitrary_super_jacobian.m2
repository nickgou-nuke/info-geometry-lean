needsPackage "Dmodules"

-- 16D Hyperplane Projection Space
R = QQ[x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16]
Q = x_1^2-x_2^2+x_3^2-x_4^2+x_5^2-x_6^2+x_7^2-x_8^2+x_9^2-x_10^2+x_11^2-x_12^2+x_13^2-x_14^2+x_15^2-x_16^2

-- The Super-Jacobian Ideal mapping the critical thermodynamic locus
J = ideal(diff(x_1, Q), diff(x_2, Q), diff(x_3, Q), diff(x_4, Q), diff(x_5, Q), diff(x_6, Q), diff(x_7, Q), diff(x_8, Q), diff(x_9, Q), diff(x_10, Q), diff(x_11, Q), diff(x_12, Q), diff(x_13, Q), diff(x_14, Q), diff(x_15, Q), diff(x_16, Q))

print "--- M2 HIGH-DIMENSIONAL SUPER-JACOBIAN START ---"
print ("Hyperplane Dimensions: " | toString(16))
print ("Dim of local critical locus J: " | toString(dim(R / J)))
print "--------------------------------------------------"
exit 0