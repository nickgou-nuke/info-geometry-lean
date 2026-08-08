# SageMath script to formalize the Cofactor Expansion of the Orientation Matrix

# Define the variables for the coordinates of three points A, B, C
R.<xA, yA, xB, yB, xC, yC> = PolynomialRing(QQ)

# Formulate the 3x3 orientation matrix
# The orientation matrix for points A(xA, yA), B(xB, yB), C(xC, yC) is:
# [ xA, yA, 1 ]
# [ xB, yB, 1 ]
# [ xC, yC, 1 ]
M = Matrix(R, [
    [xA, yA, 1],
    [xB, yB, 1],
    [xC, yC, 1]
])

# Compute the determinant of the orientation matrix
det_M = M.determinant()

# The expected expansion
expected_expansion = (xB*yC + xA*yB + yA*xC) - (yA*xB + yB*xC + xA*yC)

# Verify if they are exactly equal
is_equal = (det_M == expected_expansion)

print(f"Orientation Matrix:\n{M}\n")
print(f"Computed Determinant: {det_M}")
print(f"Expected Expansion:   {expected_expansion}")
print(f"Are they equal?       {is_equal}")

if is_equal:
    print("Proof successful: The determinant expands exactly as expected.")
else:
    print("Proof failed: The determinant does not match the expected expansion.")
