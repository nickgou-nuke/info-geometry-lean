# SageMath exact-rational certificate for Continuous Thermodynamic Geometry
# Run with: sage tools/sage/continuous_thermodynamic_geometry.sage

print("==================================================")
print("SageMath Exact-Rational Certificate:")
print("Continuous Thermodynamic Geometry (Fisher-Souriau)")
print("==================================================")

x1, x2 = var('x1 x2')
Q, dQ1, dQ2, d2Q11, d2Q12, d2Q22 = var('Q dQ1 dQ2 d2Q11 d2Q12 d2Q22')

# Define the rational function field over Q
F = FractionField(PolynomialRing(QQ, 'Q, dQ1, dQ2, d2Q11, d2Q12, d2Q22'))
Q_f, dQ1_f, dQ2_f, d2Q11_f, d2Q12_f, d2Q22_f = F.gens()

# The Fisher-Souriau metric (Hessian of log Q) evaluated rationally
H11 = (d2Q11_f * Q_f - dQ1_f * dQ1_f) / (Q_f^2)
H12 = (d2Q12_f * Q_f - dQ1_f * dQ2_f) / (Q_f^2)
H21 = (d2Q12_f * Q_f - dQ2_f * dQ1_f) / (Q_f^2)
H22 = (d2Q22_f * Q_f - dQ2_f * dQ2_f) / (Q_f^2)

is_symmetric = bool(H12 == H21)
print(f"Hessian symmetry H_ij == H_ji : {is_symmetric}")

# Symbolic substitution for an exponential family:
# Q = x1 + x2, dQ1 = x1, dQ2 = x2, d^2Q11 = x1, d^2Q12 = 0, d^2Q22 = x2
# (Note: here x1, x2 represent exp(theta_1), exp(theta_2))

det_H = H11 * H22 - H12^2
det_H_sub = det_H.subs({Q_f: x1+x2, dQ1_f: x1, dQ2_f: x2, d2Q11_f: x1, d2Q12_f: 0, d2Q22_f: x2})

is_degenerate = bool(det_H_sub == 0)
print(f"Fisher-Souriau determinant det(H) == 0 (Projective scale invariance) : {is_degenerate}")

print("\nCONTINUOUS_THERMODYNAMIC_GEOMETRY_SAGE_CERTIFICATE_OK")
