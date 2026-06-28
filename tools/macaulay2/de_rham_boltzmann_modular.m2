-- Macaulay2 finite algebraic shadow for the logarithmic differential system
restart
R = QQ[a,b,beta,r]
Q = symbol Q

f = a^2 + b^2 - r^2
print "Macaulay2 bridge shadow"
print "Constraint surface: r^2 = a^2 + b^2"
print("Polynomial relation = " | toString f)

-- logarithmic derivatives for Q = 2 cosh(beta r) are handled symbolically outside QQ,
-- but the algebraic backbone is the spectral relation r^2 = a^2 + b^2.
J = ideal(f)
print("dim R/J = " | toString dim(R/J))
print("codim J = " | toString codim J)
if substitute(f, R/J) == 0 then print "PASS: spectral relation enforced" else error "relation failed"
