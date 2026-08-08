R.<xA, yA, xB, yB, xC, yC> = PolynomialRing(QQ, 6)

# The standard 3x3 orientation matrix determinant
M = matrix([
    [xA, yA, 1],
    [xB, yB, 1],
    [xC, yC, 1]
])
det_3x3 = M.determinant()

# The efficient 2x2 determinant formula
eff_det = (xB - xA)*(yC - yA) - (xC - xA)*(yB - yA)

# Prove algebraic equivalence
is_equal = (det_3x3 == eff_det)

print("Standard 3x3 Determinant:    ", det_3x3)
print("Efficient 2x2 Determinant:   ", eff_det)
print("Algebraically Equivalent?    ", is_equal)
