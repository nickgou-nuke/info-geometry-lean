# orientability_jacobian.sage
# Formulate Orientability algebraically using the sign of the determinant of the transition Jacobian between local charts.

R.<x, y, u, v> = PolynomialRing(QQ, 4)

# Example: transition map from (u,v) to (x,y)
f1 = u^2 - v^2
f2 = 2*u*v

J = matrix([[diff(f1, u), diff(f1, v)], 
            [diff(f2, u), diff(f2, v)]])

det_J = J.determinant()
print("Jacobian matrix:")
print(J)
print("Determinant of Jacobian:")
print(det_J)
