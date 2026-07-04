var('x0 x1 x2 x3')

X = Matrix([[x0 + x1, x2 + I*x3], [x2 - I*x3, x0 - x1]])

det_X = X.det()

Q = x0^2 - x1^2 - x2^2 - x3^2

diff = (det_X - Q).simplify_full()
is_equal = bool(diff == 0)

print("Matrix X:")
print(X)
print("\nDeterminant of X:")
print(det_X.expand())
print("\nMinkowski Q:")
print(Q)
print("\nDoes det(X) match Q identically?", is_equal)
if is_equal:
    print("Proof successful: det(X) == Q")
else:
    print("Proof failed: det(X) != Q")
