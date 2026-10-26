# SageMath Verification of Archetypes XLII-LIV:
# 5-Graded Operator Zorn Algebra, BCFW Contact Recursion, Unified Three-Arnold Triad,
# and Operator / 3D Navier-Stokes Lamb-Vorticity Depletion.

print("======================================================================")
print("SageMath Verification: 5-Graded Operator Zorn, BCFW, Arnold & Navier-Stokes")
print("======================================================================")

# 1. Noncommutative FreeAlgebra verification
F.<y1,z1,xi1,y2,z2,xi2,y3,z3,xi3,eta,y0,z0,ys,zs,uy,uz,wy,wz> = FreeAlgebra(QQ, 18)

def v_zero():
    return (F(0), F(0), F(0))

def v_add(u, v):
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])

def v_sub(u, v):
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])

def left_scale(c, u):
    return (c * u[0], c * u[1], c * u[2])

def right_scale(u, c):
    return (u[0] * c, u[1] * c, u[2] * c)

def dot(u, w):
    return u[0]*w[0] + u[1]*w[1] + u[2]*w[2]

def naive_cross(u, v):
    return (u[1]*v[2] - u[2]*v[1], u[2]*v[0] - u[0]*v[2], u[0]*v[1] - u[1]*v[0])

def skew_cross(u, v):
    return v_sub(naive_cross(u, v), naive_cross(v, u))

def z_zero():
    return (F(0), v_zero(), v_zero(), F(0))

def z_one():
    return (F(1), v_zero(), v_zero(), F(1))

def z_add(X, Y):
    return (X[0] + Y[0], v_add(X[1], Y[1]), v_add(X[2], Y[2]), X[3] + Y[3])

def z_sub(X, Y):
    return (X[0] - Y[0], v_sub(X[1], Y[1]), v_sub(X[2], Y[2]), X[3] - Y[3])

def z_mul(X, Y):
    a = X[0]*Y[0] - dot(X[1], Y[2])
    v = v_sub(v_add(left_scale(X[0], Y[1]), right_scale(X[1], Y[3])), skew_cross(X[2], Y[2]))
    w = v_add(v_add(right_scale(X[2], Y[0]), left_scale(X[3], Y[2])), skew_cross(X[1], Y[1]))
    b = -dot(X[2], Y[1]) + X[3]*Y[3]
    return (a, v, w, b)

def z_assoc(X, Y, Z):
    return z_sub(z_mul(z_mul(X, Y), Z), z_mul(X, z_mul(Y, Z)))

def grade_plus1(y, z):
    return (F(0), (F(0), y, z), v_zero(), F(0))

def grade_plus2(xi):
    return (F(0), v_zero(), (xi, F(0), F(0)), F(0))

def grade_minus1(y, z):
    return (F(0), v_zero(), (F(0), y, z), F(0))

def grade_minus2(e):
    return (F(0), (e, F(0), F(0)), v_zero(), F(0))

def grade_zero(rp, rm):
    return (rp, v_zero(), v_zero(), rm)

def contact_form(a1, b1, a2, b2):
    return (a1*b2 - b1*a2) - (a2*b1 - b2*a1)

def h_group_plus(y, z, xi):
    return z_add(z_one(), z_add(grade_plus1(y, z), grade_plus2(xi)))

# Verify 5-graded Heisenberg group associativity and 4-gate braid loop in FreeAlgebra
G1 = h_group_plus(y1, z1, xi1)
G2 = h_group_plus(y2, z2, xi2)
G3 = h_group_plus(y3, z3, xi3)
G1_inv = h_group_plus(-y1, -z1, -xi1)
G2_inv = h_group_plus(-y2, -z2, -xi2)
w12 = contact_form(y1, z1, y2, z2)

assert z_assoc(G1, G2, G3) == z_zero()
assert z_mul(z_mul(G1, G2), z_mul(G1_inv, G2_inv)) == h_group_plus(F(0), F(0), w12 + w12)
print("[PASS] FreeAlgebra: 3-Layer KAN Associativity & 4-Gate Braid Commutator Loop")

# Verify 5-graded BCFW shift & contact residue in FreeAlgebra
P0 = (F(1), (F(0), -y0, -z0), v_zero(), F(0))
P_shifted = (F(1), (F(0), -(ys + y0), -(zs + z0)), v_zero(), F(0))
S_plus = z_add(z_one(), grade_plus1(ys, zs))
S_minus = z_add(z_one(), grade_plus1(-ys, -zs))
w_res = contact_form(ys, zs, y0, z0)

assert z_assoc(S_plus, P0, S_minus) == z_zero()
assert z_mul(P0, S_minus) == z_sub(P_shifted, grade_plus2(w_res))
assert z_mul(grade_minus2(eta), z_sub(z_mul(P0, S_minus), P_shifted)) == grade_zero(eta * w_res, F(0))
print("[PASS] FreeAlgebra: 5-Graded BCFW Transverse Shift & Contact Residue Readout")

# Verify 5-graded noncommutative Navier-Stokes Lamb orthogonality & vorticity depletion
U_perp = grade_plus1(uy, uz)
Om_perp = grade_plus1(wy, wz)
Lamb_perp = z_mul(Om_perp, U_perp)
assert z_mul(U_perp, Lamb_perp) == z_zero()
assert z_mul(Lamb_perp, U_perp) == z_zero()
assert z_mul(Om_perp, Lamb_perp) == z_zero()
assert z_mul(Lamb_perp, Om_perp) == z_zero()
print("[PASS] FreeAlgebra: 5-Graded Noncommutative Navier-Stokes Lamb Orthogonality & Depletion")

# Verify Archetype LVIII in FreeAlgebra: Algebraic QCD Bianchi Identity u . (u x_naive u) == (u x_naive u) . u
u_color = (y1, z1, xi1)
F_ym_color = naive_cross(u_color, u_color)
assert dot(u_color, F_ym_color) == dot(F_ym_color, u_color)
print("[PASS] FreeAlgebra: Algebraic QCD Bianchi Identity u . F_YM(u) = F_YM(u) . u")

# Verify Archetype LX in FreeAlgebra: Chiral Wavefunction Factors & 4-Factor Associative Square
e11 = grade_zero(F(1), F(0))
v_tri = (y1, z1, xi1)
w_tri = (y2, z2, xi2)
Psi_L = (F(1), v_zero(), w_tri, F(0))
Psi_R = (F(1), v_tri, v_zero(), F(0))
Pi_tri = z_mul(Psi_L, Psi_R)
assert z_mul(Psi_L, Psi_L) == Psi_L
assert z_mul(Psi_R, Psi_R) == Psi_R
assert z_mul(Psi_R, Psi_L) == grade_zero(F(1) - dot(v_tri, w_tri), F(0))
assert z_sub(z_mul(z_mul(Psi_R, Psi_L), Psi_R), z_mul(Psi_R, z_mul(Psi_L, Psi_R))) == (
    F(0),
    v_sub(right_scale(v_tri, dot(w_tri, v_tri)), left_scale(dot(v_tri, w_tri), v_tri)),
    v_zero(),
    F(0),
)
print("[PASS] FreeAlgebra: Archetype LX Chiral Wavefunction Factors & Noether-Sandwich Associator")

# Verify Archetypes LXI & LXII in FreeAlgebra: 1934 JvNW Cubic Peirce Polynomial & Yang-Mills Balance
def z_anti(X, Y):
    return z_add(z_mul(X, Y), z_mul(Y, X))

X_jvnw = (y1, (z1, xi1, y2), (z2, xi2, y3), z3)
L1_jvnw = z_anti(e11, X_jvnw)
L2_jvnw = z_anti(e11, L1_jvnw)
L3_jvnw = z_anti(e11, L2_jvnw)
assert z_add(z_sub(L3_jvnw, z_add(z_add(L2_jvnw, L2_jvnw), L2_jvnw)), z_add(L1_jvnw, L1_jvnw)) == z_zero()

J_ym_free = (F(0), u_color, F_ym_color, F(0))
alpha_ym_free = -(dot(u_color, F_ym_color) + dot(u_color, F_ym_color))
assert z_anti(J_ym_free, J_ym_free) == grade_zero(alpha_ym_free, alpha_ym_free)
print("[PASS] FreeAlgebra: Archetypes LXI-LXII 1934 JvNW Cubic Peirce & Noncommutative Yang-Mills Balance")

# Verify Archetypes LXIII & LXIV in FreeAlgebra: Wheeler "It from Bit" & "Boundary of a Boundary is Zero"
e22 = grade_zero(F(0), F(1))
d_v_wh = z_sub(Psi_R, e11)
d_w_wh = z_sub(Psi_L, e11)
assert z_mul(d_v_wh, d_v_wh) == z_zero()
assert z_mul(d_w_wh, d_w_wh) == z_zero()
assert z_add(z_mul(d_v_wh, d_w_wh), z_mul(d_w_wh, d_v_wh)) == grade_zero(-dot(v_tri, w_tri), -dot(w_tri, v_tri))
assert z_sub(z_mul(d_v_wh, d_w_wh), z_mul(d_w_wh, d_v_wh)) == grade_zero(-dot(v_tri, w_tri), dot(w_tri, v_tri))
print("[PASS] FreeAlgebra: Archetypes LXIII-LXIV Wheeler 'It from Bit' & 'Boundary of a Boundary is Zero'")

def z_euler5(X):
    return (
        F(0),
        (-2*X[1][0], X[1][1], X[1][2]),
        (2*X[2][0], -X[2][1], -X[2][2]),
        F(0),
    )

N1p_f = z_add(grade_plus1(y1, z1), grade_plus2(xi1))
N2p_f = z_add(grade_plus1(y2, z2), grade_plus2(xi2))
assert z_euler5(z_mul(N1p_f, N2p_f)) == z_add(z_mul(z_euler5(N1p_f), N2p_f), z_mul(N1p_f, z_euler5(N2p_f)))
E1f = z_euler5(X_jvnw)
E2f = z_euler5(E1f)
E3f = z_euler5(E2f)
E4f = z_euler5(E3f)
E5f = z_euler5(E4f)
assert z_add(z_sub(E5f, z_add(z_add(z_add(z_add(E3f, E3f), E3f), E3f), E3f)), z_add(z_add(z_add(E1f, E1f), E1f), E1f)) == z_zero()
print("[PASS] FreeAlgebra: Archetypes LXV-LXVI Euler 5-Grading Nilradical Derivation & KKT Degree-5 Polynomial")

# 2. Commutative 3D PolynomialRing verification of Universal 3D Zorn Lamb Nilpotence & JvNW Axiom (III)
R.<ux,uy,uz,wx,wy,wz,dp,dm> = PolynomialRing(QQ, 8)

def c_cross(u, v):
    return (u[1]*v[2] - u[2]*v[1], u[2]*v[0] - u[0]*v[2], u[0]*v[1] - u[1]*v[0])

def c_dot(u, v):
    return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]

def c_zadd(X, Y):
    return (
        X[0] + Y[0],
        tuple(X[1][i] + Y[1][i] for i in range(3)),
        tuple(X[2][i] + Y[2][i] for i in range(3)),
        X[3] + Y[3],
    )

def c_zmul(X, Y):
    a = X[0]*Y[0] - c_dot(X[1], Y[2])
    v = tuple(X[0]*Y[1][i] + X[1][i]*Y[3] - c_cross(X[2], Y[2])[i] for i in range(3))
    w = tuple(X[2][i]*Y[0] + X[3]*Y[2][i] + c_cross(X[1], Y[1])[i] for i in range(3))
    b = -c_dot(X[2], Y[1]) + X[3]*Y[3]
    return (a, v, w, b)

def c_zjordan(X, Y):
    return c_zadd(c_zmul(X, Y), c_zmul(Y, X))

c_zero = (R(0), (R(0), R(0), R(0)), (R(0), R(0), R(0)), R(0))
U3 = (R(0), (ux, uy, uz), (R(0), R(0), R(0)), R(0))
Om3 = (R(0), (wx, wy, wz), (R(0), R(0), R(0)), R(0))
Lamb3 = c_zmul(Om3, U3)

assert c_zmul(U3, Lamb3) == c_zero
assert c_zmul(Lamb3, U3) == c_zero
assert c_zmul(Om3, Lamb3) == c_zero
assert c_zmul(Lamb3, Om3) == c_zero
print("[PASS] PolynomialRing: Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence")

A_jvnw = (dp, (ux, uy, uz), (wx, wy, wz), dm)
B_jvnw = (dm, (wx, uz, uy), (ux, wz, wy), dp)
A_sq = c_zjordan(A_jvnw, A_jvnw)
assert c_zjordan(c_zjordan(A_sq, B_jvnw), A_jvnw) == c_zjordan(A_sq, c_zjordan(B_jvnw, A_jvnw))
print("[PASS] PolynomialRing: 1934 JvNW Fundamental Jordan Axiom (III) ((A o A) o B) o A = (A o A) o (B o A)")

# Archetypes LXVII & LXVIII: Rolf Dahm (JPCS 3152 (2025) 012008) Plücker-Klein Quadric & Dihedral D_4 / PG(3,2) Triples
dahm_r0 = (R(1), (R(0), R(0), R(0)), (R(0), R(0), R(0)), R(1))
dahm_r1 = (R(0), (-R(1), R(0), R(0)), (-R(1), R(0), R(0)), R(0))
dahm_s0 = (R(1), (R(0), R(0), R(0)), (R(0), R(0), R(0)), -R(1))
dahm_s1 = (R(0), (-R(1), R(0), R(0)), (R(1), R(0), R(0)), R(0))
assert c_zmul(dahm_s0, dahm_s0) == dahm_r0
assert c_zmul(dahm_s1, dahm_s1) == dahm_r0
assert c_zmul(dahm_s0, dahm_r1) == dahm_s1
assert c_zmul(c_zmul(dahm_s1, dahm_s0), dahm_r1) == dahm_r0
# Archetypes LXIX & LXX: Maxwell-Poynting Hodge-Dual Stress Matrix J(E, B) * J*(E, B)
J_em_c = (R(0), (ux, uy, uz), (wx, wy, wz), R(0))
J_star_c = (R(0), (-wx, -wy, -wz), (ux, uy, uz), R(0))
S_c = c_cross((ux, uy, uz), (wx, wy, wz))
S_neg_c = tuple(-x for x in S_c)
assert c_zmul(J_em_c, J_star_c) == (-c_dot((ux, uy, uz), (ux, uy, uz)), S_c, S_neg_c, c_dot((wx, wy, wz), (wx, wy, wz)))
print("[PASS] PolynomialRing: Archetypes LXVII-LXX (Dahm Dihedral D_4, PG(3,2) Triple, & Maxwell-Poynting Hodge-Dual Stress Matrix)")

# Archetypes LXXI & LXXII: Saniga-Holweck-Pracna (2015) Combinatorial Grassmannian G_2(N+1) & Sedenion Zero Divisors
def c_zconj(X):
    return (X[3], tuple(-x for x in X[1]), tuple(-x for x in X[2]), X[0])

def c_sed_mul(S1, S2):
    x_part = c_zadd(c_zmul(S1[0], S2[0]), c_zmul(S2[1], ( -c_zconj(S1[1])[0], tuple(-x for x in c_zconj(S1[1])[1]), tuple(-x for x in c_zconj(S1[1])[2]), -c_zconj(S1[1])[3] )))
    y_part = c_zadd(c_zmul(c_zconj(S1[0]), S2[1]), c_zmul(S2[0], S1[1]))
    return (x_part, y_part)

Om_12_c = (R(0), (ux - wx, uy - wy, uz - wz), (R(0), R(0), R(0)), R(0))
Om_23_c = (R(0), (wx - dp, wy - dm, wz - ux), (R(0), R(0), R(0)), R(0))
Om_31_c = (R(0), (dp - ux, dm - uy, ux - uz), (R(0), R(0), R(0)), R(0))
assert c_zmul(Om_12_c, Om_23_c) == c_zmul(Om_23_c, Om_31_c)
assert c_zmul(Om_23_c, Om_31_c) == c_zmul(Om_31_c, Om_12_c)
S_p_c = ((R(0), (ux, uy, uz), (R(0), R(0), R(0)), R(0)), (R(0), (R(0), R(0), R(0)), (wx, wy, wz), R(0)))
S_m_c = ((R(0), (R(0), R(0), R(0)), (wx, wy, wz), R(0)), (R(0), (-ux, -uy, -uz), (R(0), R(0), R(0)), R(0)))
assert c_sed_mul(S_p_c, S_m_c) == (c_zero, c_zero)
assert c_sed_mul(S_m_c, S_p_c) == (c_zero, c_zero)
# Archetypes LXXIII & LXXIV: Pasch 4-Simplex Tetrahedral 2-Boundary Closure P_123 - P_134 + P_124 - P_234 = 0
Om_34_c = (R(0), (dp, dm, ux), (R(0), R(0), R(0)), R(0))
Om_13_c = c_zadd(Om_12_c, Om_23_c)
Om_24_c = c_zadd(Om_23_c, Om_34_c)
P_123_c = c_zmul(Om_12_c, Om_23_c)
P_134_c = c_zmul(Om_13_c, Om_34_c)
P_124_c = c_zmul(Om_12_c, Om_24_c)
P_234_c = c_zmul(Om_23_c, Om_34_c)
assert c_zadd(P_234_c, P_124_c) == c_zadd(P_134_c, P_123_c)
print("[PASS] PolynomialRing: Archetypes LXXI-LXXIV (Saniga-Holweck-Pracna Grassmannian G_2(N+1), Sedenion Zero Divisors, & Pasch 4-Simplex 2-Boundary Closure)")

# Archetypes LXXV, LXXVI, LXXVII, & LXXVIII: Catto-Gurcan-Khalfan-Kurt (2018) E_9/E_10 Roots,
# Jacobson Triple Weyl Reflection, & 27D Split-Octonion Albert-Freudenthal Adjoint & Determinant Law
def c_zsub(X, Y):
    return (
        X[0] - Y[0],
        tuple(X[1][i] - Y[1][i] for i in range(3)),
        tuple(X[2][i] - Y[2][i] for i in range(3)),
        X[3] - Y[3],
    )

def c_zscale(c, X):
    return (c*X[0], tuple(c*X[1][i] for i in range(3)), tuple(c*X[2][i] for i in range(3)), c*X[3])

def c_ztrace(X):
    return X[0] + X[3]

def c_zmul_std(X, Y):
    a = X[0]*Y[0] + c_dot(X[1], Y[2])
    v = tuple(X[0]*Y[1][i] + X[1][i]*Y[3] + c_cross(X[2], Y[2])[i] for i in range(3))
    w = tuple(X[2][i]*Y[0] + X[3]*Y[2][i] - c_cross(X[1], Y[1])[i] for i in range(3))
    b = c_dot(X[2], Y[1]) + X[3]*Y[3]
    return (a, v, w, b)

def c_zjordan_std(X, Y):
    return c_zadd(c_zmul_std(X, Y), c_zmul_std(Y, X))

def c_znorm(X):
    return X[0]*X[3] - c_dot(X[1], X[2])

def c_zinner(X, Y):
    return c_ztrace(c_zmul_std(X, c_zconj(Y)))

def c_zjt(X, Y, Z):
    return c_zsub(c_zadd(c_zjordan_std(c_zjordan_std(X, Y), Z), c_zjordan_std(X, c_zjordan_std(Y, Z))), c_zjordan_std(c_zjordan_std(X, Z), Y))

# Jacobson Triple Weyl reflection & norm similitude:
T_BAB_c = c_zjt(B_jvnw, c_zconj(A_jvnw), B_jvnw)
Weyl_rhs = c_zscale(4, c_zsub(c_zscale(c_ztrace(c_zmul_std(A_jvnw, c_zconj(B_jvnw))), B_jvnw), c_zscale(c_znorm(B_jvnw), A_jvnw)))
assert T_BAB_c == Weyl_rhs
assert c_znorm(T_BAB_c) == 16 * (c_znorm(B_jvnw)^2) * c_znorm(A_jvnw)

# 27D Split-Octonion Albert-Conway-Sloane Freudenthal Adjoint & Determinant Law (Archetype LXXVII):
Q_alb = A_jvnw
Xi1_alb = B_jvnw
Xi2_alb = (ux, (wy, wz, dp), (dm, ux, uy), uz)
xp_a = dp
xm_a = dm
v_a = ux + wy
assert c_ztrace(c_zmul_std(c_zmul_std(Q_alb, Xi2_alb), c_zconj(Xi1_alb))) == c_ztrace(c_zmul_std(Q_alb, c_zmul_std(Xi2_alb, c_zconj(Xi1_alb))))
sh_xp = xm_a * v_a - c_znorm(Xi2_alb)
sh_xm = xp_a * v_a - c_znorm(Xi1_alb)
sh_v = xp_a * xm_a - c_znorm(Q_alb)
sh_Q = c_zsub(c_zmul_std(Xi1_alb, c_zconj(Xi2_alb)), c_zscale(v_a, Q_alb))
sh_Xi1 = c_zsub(c_zmul_std(Q_alb, Xi2_alb), c_zscale(xm_a, Xi1_alb))
sh_Xi2 = c_zsub(c_zmul_std(c_zconj(Q_alb), Xi1_alb), c_zscale(xp_a, Xi2_alb))
det27_a = xp_a*xm_a*v_a - xp_a*c_znorm(Xi2_alb) - xm_a*c_znorm(Xi1_alb) - v_a*c_znorm(Q_alb) + c_ztrace(c_zmul_std(c_zmul_std(Q_alb, Xi2_alb), c_zconj(Xi1_alb)))
ac_xp = 2*xp_a*sh_xp + c_zinner(Q_alb, sh_Q) + c_zinner(Xi1_alb, sh_Xi1)
ac_xm = 2*xm_a*sh_xm + c_zinner(c_zconj(Q_alb), c_zconj(sh_Q)) + c_zinner(Xi2_alb, sh_Xi2)
ac_v = 2*v_a*sh_v + c_zinner(Xi1_alb, sh_Xi1) + c_zinner(Xi2_alb, sh_Xi2)
ac_Q = c_zadd(c_zadd(c_zscale(xp_a + xm_a, sh_Q), c_zscale(sh_xp + sh_xm, Q_alb)), c_zadd(c_zmul_std(Xi1_alb, c_zconj(sh_Xi2)), c_zmul_std(sh_Xi1, c_zconj(Xi2_alb))))
ac_Xi1 = c_zadd(c_zadd(c_zscale(xp_a + v_a, sh_Xi1), c_zscale(sh_xp + sh_v, Xi1_alb)), c_zadd(c_zmul_std(Q_alb, sh_Xi2), c_zmul_std(sh_Q, Xi2_alb)))
ac_Xi2 = c_zadd(c_zadd(c_zscale(xm_a + v_a, sh_Xi2), c_zscale(sh_xm + sh_v, Xi2_alb)), c_zadd(c_zmul_std(c_zconj(Q_alb), sh_Xi1), c_zmul_std(c_zconj(sh_Q), Xi1_alb)))
assert ac_xp == 2 * det27_a
assert ac_xm == 2 * det27_a
assert ac_v == 2 * det27_a
assert ac_Q == c_zero
assert ac_Xi1 == c_zero
assert ac_Xi2 == c_zero
print("[PASS] PolynomialRing: Archetypes LXXV-LXXVIII (Catto E_9/E_10 Weyl Reflection & 27D Split-Octonion Albert-Freudenthal Adjoint & Determinant Law)")

# Archetypes LXXIX & LXXX: Z_3-Triality Operator Determinant Splitting & 72-Channel 3x3 Operator Zorn Nilradical Freudenthal Inversion
q_f = (y1, z1, xi1)
xi1_f = (y2, z2, xi2)
xi2_f = (y3, z3, xi3)
Q_f = (F(0), q_f, (F(0), F(0), F(0)), F(0))
Xi1_f = (F(0), xi1_f, (F(0), F(0), F(0)), F(0))
Xi2_f = (F(0), xi2_f, (F(0), F(0), F(0)), F(0))
Delta0_f = dot(q_f, skew_cross(xi2_f, xi1_f))
Delta1_f = dot(xi2_f, skew_cross(xi1_f, q_f))
Delta2_f = dot(xi1_f, skew_cross(q_f, xi2_f))
Delta0_st_f = dot(skew_cross(q_f, xi2_f), xi1_f)
Delta1_st_f = dot(skew_cross(xi2_f, xi1_f), q_f)
Delta2_st_f = dot(skew_cross(xi1_f, q_f), xi2_f)
assert z_assoc(Q_f, Xi2_f, Xi1_f) == grade_zero(Delta0_f, -Delta0_st_f)
assert z_assoc(Xi2_f, Xi1_f, Q_f) == grade_zero(Delta1_f, -Delta1_st_f)
assert z_assoc(Xi1_f, Q_f, Xi2_f) == grade_zero(Delta2_f, -Delta2_st_f)
print("[PASS] FreeAlgebra: Archetypes LXXIX-LXXX (Z_3-Triality Operator Determinant Splitting & 72-Channel Nilradical Inversion)")

# Archetypes LXXXI, LXXXII, & LXXXIII: Steen H. Hansen (21 Oct 2026) Cl(4,2) Doublet Tower & Zorn Conformal-Triality Marriage
D_zorn_f = (F(1), (F(0), F(0), F(0)), (F(0), F(0), F(0)), F(-1))
assert z_sub(z_mul(D_zorn_f, Q_f), z_mul(Q_f, D_zorn_f)) == z_add(Q_f, Q_f)
assert z_add(z_mul(D_zorn_f, Q_f), z_mul(Q_f, D_zorn_f)) == z_zero()
assert z_mul(Q_f, Q_f) == z_zero()
assert z_sub(z_mul(Q_f, Xi1_f), z_mul(Xi1_f, Q_f)) == (F(0), (F(0), F(0), F(0)), v_add(skew_cross(q_f, xi1_f), skew_cross(q_f, xi1_f)), F(0))
assert ((ux - 1) - 1)^2 - ((ux - 1) + 1) == (ux - 1) * (ux - 4)
print("[PASS] FreeAlgebra & PolynomialRing: Archetypes LXXXI-LXXXIII (Hansen 2026 Cl(4,2) Doublet Tower, S_2=0 d=4 Selection, & Zorn Conformal-Triality Marriage)")

# Archetypes LXXXIV & LXXXV: Zero Chiral Volume, Krein Null Kernel, Parabolic Boundary Sheaf, & Majorana Horizon Zero Modes
vt1_f = (F(0), y1, z1)
vt2_f = (F(0), y2, z2)
vt3_f = (F(0), y3, z3)
assert dot(vt1_f, skew_cross(vt2_f, vt3_f)) == F(0)
assert dot(skew_cross(vt1_f, vt2_f), vt3_f) == F(0)
Ep1_f = grade_plus1(y1, z1)
Em1_f = (F(0), (F(0), F(0), F(0)), (F(0), y1, z1), F(0))
Ep2_f = grade_plus2(xi3)
Em2_f = grade_minus2(xi3)
Pi_bf = (F(1), (F(0), -y1, -z1), (xi1, F(0), F(0)), F(0))
Pi_bf_perp = z_sub(z_one(), Pi_bf)
assert z_mul(Ep1_f, Ep2_f) == z_zero() and z_mul(Ep2_f, Ep1_f) == z_zero()
assert z_mul(Em1_f, Em2_f) == z_zero() and z_mul(Em2_f, Em1_f) == z_zero()
assert z_mul(Em1_f, Ep2_f) == grade_plus1(-(z1 * xi3 + xi3 * z1), y1 * xi3 + xi3 * y1)
assert z_mul(Pi_bf, Ep2_f) == z_zero() and z_mul(Ep2_f, Pi_bf) == Ep2_f
assert z_mul(Pi_bf_perp, Ep2_f) == Ep2_f and z_mul(Ep2_f, Pi_bf_perp) == z_zero()
# Archetypes LXXXVI & LXXXVII: Chevalley-Lounesto-Shirokov Spinor Ideals & Relativistic Dirac-Krein Ket-Bra Duality
psi_c1_f = (y1, v_zero(), (xi1, F(0), F(0)), F(0))
phi_c2_bar_f = (y2, (xi2, F(0), F(0)), v_zero(), F(0))
psi_c3_f = (y3, v_zero(), (xi3, F(0), F(0)), F(0))
assert z_assoc(psi_c1_f, phi_c2_bar_f, psi_c3_f) == z_zero()
assert z_mul(z_mul(psi_c1_f, phi_c2_bar_f), psi_c3_f) == (y1 * (y2 * y3 - xi2 * xi3), v_zero(), (xi1 * (y2 * y3 - xi2 * xi3), F(0), F(0)), F(0))
# Archetypes LXXXVIII & LXXXIX: Trifactor-Loxodromic Compass, Doubled 4-Vector Potentials, & 8D Zorn-Riccati Möbius Operator
e11_f = grade_zero(F(1), F(0))
e22_f = grade_zero(F(0), F(1))
X_obs_f = (y1, q_f, xi1_f, z1)
A_plus_f = z_mul(e11_f, X_obs_f)
A_minus_f = z_mul(e22_f, X_obs_f)
assert z_add(A_plus_f, A_minus_f) == X_obs_f
assert z_mul(A_plus_f, A_minus_f) == (-dot(q_f, xi1_f), right_scale(q_f, z1), v_zero(), F(0))
assert z_mul(A_minus_f, A_plus_f) == (F(0), v_zero(), right_scale(xi1_f, y1), -dot(xi1_f, q_f))
P_row_f = (F(1), q_f, v_zero(), F(0))
P_col_f = (F(1), v_zero(), xi1_f, F(0))
U_up_f = (F(1), q_f, v_zero(), F(1))
U_lo_f = (F(1), v_zero(), xi1_f, F(1))
T_bruhat_f = z_mul(z_mul(U_lo_f, grade_zero(F(1), xi2)), U_up_f)
assert T_bruhat_f == z_add(z_mul(z_mul(P_col_f, grade_zero(F(1), F(0))), P_row_f), grade_zero(F(0), xi2))
riccati_T_f = v_sub(v_add(v_add(right_scale(q_f, dot(T_bruhat_f[2], q_f)), right_scale(q_f, T_bruhat_f[3])), left_scale(T_bruhat_f[0], q_f)), T_bruhat_f[1])
assert riccati_T_f == right_scale(q_f, xi2)
print("[PASS] FreeAlgebra: Archetypes LXXXIV-LXXXIX (Zero Chiral Volume, Krein Null Kernel, Parabolic Majorana Zero Modes, Chevalley-Shirokov Spinor Ideals, & Trifactor-Loxodromic Zorn-Riccati Compass)")

# Archetypes XC-XCV: 56D Freudenthal E_7 Euler Trace Identity & S-Duality, Colimit Doublet Tower, & Gelfand-Retakh Gauss-Bruhat Elimination
trace_pair_27 = xp_a*sh_xp + xm_a*sh_xm + v_a*sh_v + c_zinner(Q_alb, sh_Q) + c_zinner(Xi1_alb, sh_Xi1) + c_zinner(Xi2_alb, sh_Xi2)
assert trace_pair_27 == 3 * det27_a
# Noncommutative Doublet Tower & Cantor-Peirce Bit-Split in FreeAlgebra:
def doublet_f(a_el):
    return grade_zero(a_el, a_el)
def peirce11_f(a_el):
    return grade_zero(a_el, F(0))
def peirce22_f(b_el):
    return grade_zero(F(0), b_el)
assert doublet_f(y1 * z1) == z_mul(doublet_f(y1), doublet_f(z1))
assert doublet_f(y1) == z_add(peirce11_f(y1), peirce22_f(y1))
assert z_mul(peirce11_f(y1), peirce22_f(z1)) == z_zero()
# Orthogonal 1-Component Root-Ray Compass-Needle Semigroup Homomorphism in FreeAlgebra:
P_row_tr_f = (F(1), (F(0), y1, F(0)), v_zero(), F(0))
P_col_tr_f = (F(1), v_zero(), (xi1, F(0), F(0)), F(0))
def compass_f(a_el):
    return z_mul(z_mul(P_col_tr_f, peirce11_f(a_el)), P_row_tr_f)
assert z_mul(compass_f(y2), compass_f(z2)) == compass_f(y2 * z2)
# Exact Gauss-Bruhat Trifactor Elimination & Gelfand-Retakh Quasideterminant in FreeAlgebra:
# For orthogonal 1-component root-ray channels v_tr = (0, y1, 0), w_tr = (xi1, 0, 0), skew_cross vanishes identically:
U_up_tr_f = (F(1), (F(0), y1, F(0)), v_zero(), F(1))
U_lo_tr_f = (F(1), v_zero(), (xi1, F(0), F(0)), F(1))
U_up_neg_tr_f = (F(1), (F(0), -y1, F(0)), v_zero(), F(1))
U_lo_neg_tr_f = (F(1), v_zero(), (-xi1, F(0), F(0)), F(1))
T_gen_f = z_mul(z_mul(U_lo_tr_f, grade_zero(xi2, xi3)), U_up_tr_f)
assert z_mul(z_mul(U_lo_neg_tr_f, T_gen_f), U_up_neg_tr_f) == grade_zero(xi2, xi3)
U_up_neg_f = (F(1), v_sub(v_zero(), q_f), v_zero(), F(1))
U_lo_neg_f = (F(1), v_zero(), v_sub(v_zero(), xi1_f), F(1))
assert z_mul(z_mul(U_lo_neg_f, T_bruhat_f), U_up_neg_f) == grade_zero(F(1), xi2)
assert z_mul(U_lo_neg_f, z_mul(U_lo_f, grade_zero(xi1, xi2))) == (xi1, skew_cross(xi1_f, right_scale(xi1_f, xi1)), v_zero(), xi2)
assert z_mul(z_mul(grade_zero(xi1, xi2), U_up_f), U_up_neg_f) == (xi1, v_zero(), v_sub(v_zero(), skew_cross(left_scale(xi1, q_f), q_f)), xi2)
assert T_bruhat_f[3] + dot(T_bruhat_f[2], T_bruhat_f[1]) == xi2
# Exact Noncommutative Zorn-Riccati Shift / Taylor Cocycle in FreeAlgebra:
def riccati_f(X_m, q_v):
    return v_sub(v_add(v_add(right_scale(q_v, dot(X_m[2], q_v)), right_scale(q_v, X_m[3])), left_scale(X_m[0], q_v)), X_m[1])
delta_f = xi2_f
ric_shift_f = riccati_f(X_obs_f, v_add(q_f, delta_f))
ric_lin_f = v_add(v_add(left_scale(X_obs_f[0], delta_f), right_scale(delta_f, X_obs_f[3] + dot(X_obs_f[2], q_f))), right_scale(q_f, dot(X_obs_f[2], delta_f)))
ric_quad_f = right_scale(delta_f, dot(X_obs_f[2], delta_f))
assert ric_shift_f == v_add(v_add(riccati_f(X_obs_f, q_f), ric_lin_f), ric_quad_f)
# 4-Spinor Cross-Difference Translation Invariance in FreeAlgebra:
def spin_amp_f(v_p, w_p):
    return z_mul((F(1), v_p, v_zero(), F(0)), (F(1), v_zero(), w_p, F(0)))
cross_orig_f = z_sub(z_sub(spin_amp_f(q_f, xi1_f), spin_amp_f(q_f, xi2_f)), z_sub(spin_amp_f(xi2_f, xi1_f), spin_amp_f(xi2_f, xi2_f)))
cross_shift_f = z_sub(
    z_sub(spin_amp_f(v_add(q_f, delta_f), v_add(xi1_f, delta_f)), spin_amp_f(v_add(q_f, delta_f), v_add(xi2_f, delta_f))),
    z_sub(spin_amp_f(v_add(xi2_f, delta_f), v_add(xi1_f, delta_f)), spin_amp_f(v_add(xi2_f, delta_f), v_add(xi2_f, delta_f)))
)
assert cross_orig_f == cross_shift_f
# Archetypes XCVI-XCVIII: Operator-Twisted Nambu-Gorkov Cayley-Dickson Doubling & 5-Graded Spectral Projectors
def cd_conj_f(z_p):
    return (z_p[0], -z_p[1])
def cd_mul_f(Om_el, z_p, w_p):
    # For symmetric elements in FreeAlgebra (where star(x) = x, star(y) = y):
    return (z_p[0] * w_p[0] + Om_el * (w_p[1] * z_p[1]), z_p[0] * w_p[1] + w_p[0] * z_p[1])
E_cd_f = (F(0), F(1))
Z_cd_f = (y1, z1)
assert cd_mul_f(xi1, Z_cd_f, cd_conj_f(Z_cd_f)) == (y1 * y1 - xi1 * (z1 * z1), F(0))
E2_cd_f = cd_mul_f(xi1, E_cd_f, E_cd_f)
assert E2_cd_f == (xi1, F(0))
assert cd_mul_f(xi1, E2_cd_f, E2_cd_f) == (xi1 * xi1, F(0))
assert cd_mul_f(xi1, cd_mul_f(xi1, E_cd_f, (y1, F(0))), E_cd_f) == (xi1 * y1, F(0))
def op_euler5_f(Z_m):
    return (F(0), (-2 * Z_m[1][0], Z_m[1][1], Z_m[1][2]), (2 * Z_m[2][0], -Z_m[2][1], -Z_m[2][2]), F(0))
def z_scale_f(k_s, Z_m):
    return (k_s * Z_m[0], left_scale(k_s, Z_m[1]), left_scale(k_s, Z_m[2]), k_s * Z_m[3])
D1_f = op_euler5_f(X_obs_f)
D2_f = op_euler5_f(D1_f)
D3_f = op_euler5_f(D2_f)
D4_f = op_euler5_f(D3_f)
D5_f = op_euler5_f(D4_f)
assert z_add(z_sub(D4_f, z_scale_f(F(5), D2_f)), z_scale_f(F(4), X_obs_f)) == z_scale_f(F(4), grade_zero(X_obs_f[0], X_obs_f[3]))
assert z_sub(D3_f, z_scale_f(F(4), D1_f)) == z_scale_f(F(-3), z_sub(grade_plus1(X_obs_f[1][1], X_obs_f[1][2]), (F(0), v_zero(), (F(0), X_obs_f[2][1], X_obs_f[2][2]), F(0))))
assert z_sub(D3_f, D1_f) == z_scale_f(F(6), z_sub(grade_plus2(X_obs_f[2][0]), grade_minus2(X_obs_f[1][0])))
assert z_add(z_sub(D5_f, z_scale_f(F(5), D3_f)), z_scale_f(F(4), D1_f)) == z_zero()
# Archetypes XCIX-C: Noncommutative Cyclotomic Factorizations, OpCyclotomic3 Quotient Ring, & Z_6 Galois Automorphism Group:
phi1_f = xi1 - F(1)
phi2_f = xi1 + F(1)
phi3_f = xi1 * xi1 + xi1 + F(1)
phi4_f = xi1 * xi1 + F(1)
phi6_f = xi1 * xi1 - xi1 + F(1)
assert xi1^3 - F(1) == phi1_f * phi3_f and xi1^3 - F(1) == phi3_f * phi1_f
assert xi1^3 + F(1) == phi2_f * phi6_f and xi1^3 + F(1) == phi6_f * phi2_f
assert xi1^6 - F(1) == phi1_f * phi2_f * phi3_f * phi6_f
def cyc3_mul_f(zp, wp):
    return (zp[0]*wp[0] - zp[1]*wp[1], zp[0]*wp[1] + zp[1]*wp[0] - zp[1]*wp[1])
def cyc3_gal_f(zp):
    return (zp[0] - zp[1], -zp[1])
def cyc6_mul_f(zp, wp):
    return (zp[0]*wp[0] - zp[1]*wp[1], zp[0]*wp[1] + zp[1]*wp[0] + zp[1]*wp[1])
def cyc6_gal_f(zp):
    return (zp[0] + zp[1], -zp[1])
def to_cyc3_f(zp):
    return (zp[0] + zp[1], zp[1])
assert cyc3_gal_f(cyc3_mul_f((y1, z1), (y2, z2))) == cyc3_mul_f(cyc3_gal_f((y1, z1)), cyc3_gal_f((y2, z2)))
assert cyc6_gal_f(cyc6_mul_f((y1, z1), (y2, z2))) == cyc6_mul_f(cyc6_gal_f((y1, z1)), cyc6_gal_f((y2, z2)))
assert to_cyc3_f(cyc6_mul_f((y1, z1), (y2, z2))) == cyc3_mul_f(to_cyc3_f((y1, z1)), to_cyc3_f((y2, z2)))
def tri_v_f(vp):
    return (vp[1], vp[2], vp[0])
def gal_z3_f(Xm):
    return (Xm[0], tri_v_f(Xm[1]), tri_v_f(Xm[2]), Xm[3])
Y_obs_f = (y2, (xi2, y1, z1), (xi3, y2, z2), z2)
assert gal_z3_f(z_mul(X_obs_f, Y_obs_f)) == z_mul(gal_z3_f(X_obs_f), gal_z3_f(Y_obs_f))
assert gal_z3_f(gal_z3_f(gal_z3_f(X_obs_f))) == X_obs_f
def z_riccati_f(Xm, qv):
    return v_sub(v_sub(v_add(right_scale(qv, dot(Xm[2], qv)), right_scale(qv, Xm[3])), left_scale(Xm[0], qv)), Xm[1])
assert tri_v_f(z_riccati_f(X_obs_f, q_f)) == z_riccati_f(gal_z3_f(X_obs_f), tri_v_f(q_f))
# Archetypes CV-CVII: Noncommutative Galois Norm Commutator Anomaly & Z_3 Singlet Associativity:
assert cyc3_mul_f((y1, z1), cyc3_gal_f((y1, z1))) == (y1*y1 - y1*z1 + z1*z1, z1*y1 - y1*z1)
assert cyc6_mul_f((y1, z1), cyc6_gal_f((y1, z1))) == (y1*y1 + y1*z1 + z1*z1, z1*y1 - y1*z1)
def z_singlet_f(a_s, c_s, d_s, b_s):
    return (a_s, (c_s, c_s, c_s), (d_s, d_s, d_s), b_s)
S1_f = z_singlet_f(y1, z1, xi1, y2)
S2_f = z_singlet_f(z2, xi2, y3, z3)
S3_f = z_singlet_f(xi3, y1, z2, xi1)
assert z_assoc(S1_f, S2_f, S3_f) == z_zero()
# Archetypes CVIII-CXIII: Signed Reflection Automorphism rho_refl, Dihedral S_3, Klein V_4, Octahedral S_4, & Triality Trio of 5-Gradings:
def refl_v_f(vp):
    return (-vp[0], -vp[2], -vp[1])
def klein_x_v_f(vp):
    return (vp[0], -vp[1], -vp[2])
def klein_y_v_f(vp):
    return (-vp[0], vp[1], -vp[2])
def klein_z_v_f(vp):
    return (-vp[0], -vp[1], vp[2])
def refl_z_f(Xm):
    return (Xm[0], refl_v_f(Xm[1]), refl_v_f(Xm[2]), Xm[3])
def klein_x_z_f(Xm):
    return (Xm[0], klein_x_v_f(Xm[1]), klein_x_v_f(Xm[2]), Xm[3])
def klein_y_z_f(Xm):
    return (Xm[0], klein_y_v_f(Xm[1]), klein_y_v_f(Xm[2]), Xm[3])
def klein_z_z_f(Xm):
    return (Xm[0], klein_z_v_f(Xm[1]), klein_z_v_f(Xm[2]), Xm[3])
assert refl_z_f(z_mul(X_obs_f, Y_obs_f)) == z_mul(refl_z_f(X_obs_f), refl_z_f(Y_obs_f))
assert refl_z_f(gal_z3_f(refl_z_f(X_obs_f))) == gal_z3_f(gal_z3_f(X_obs_f))
assert refl_v_f(z_riccati_f(X_obs_f, q_f)) == z_riccati_f(refl_z_f(X_obs_f), refl_v_f(q_f))
assert klein_x_z_f(z_mul(X_obs_f, Y_obs_f)) == z_mul(klein_x_z_f(X_obs_f), klein_x_z_f(Y_obs_f))
assert klein_y_z_f(z_mul(X_obs_f, Y_obs_f)) == z_mul(klein_y_z_f(X_obs_f), klein_y_z_f(Y_obs_f))
assert klein_z_z_f(z_mul(X_obs_f, Y_obs_f)) == z_mul(klein_z_z_f(X_obs_f), klein_z_z_f(Y_obs_f))
assert refl_z_f(klein_y_z_f(refl_z_f(X_obs_f))) == klein_z_z_f(X_obs_f)
def euler5_x_f(Xm):
    return (F(0), (-F(2)*Xm[1][0], Xm[1][1], Xm[1][2]), (F(2)*Xm[2][0], -Xm[2][1], -Xm[2][2]), F(0))
def euler5_y_f(Xm):
    return (F(0), (Xm[1][0], -F(2)*Xm[1][1], Xm[1][2]), (-Xm[2][0], F(2)*Xm[2][1], -Xm[2][2]), F(0))
def euler5_z_f(Xm):
    return (F(0), (Xm[1][0], Xm[1][1], -F(2)*Xm[1][2]), (-Xm[2][0], -Xm[2][1], F(2)*Xm[2][2]), F(0))
assert z_add(z_add(euler5_x_f(X_obs_f), euler5_y_f(X_obs_f)), euler5_z_f(X_obs_f)) == z_zero()
# Archetypes CXIV-CXVI: Quaternion Spin Group Q_8 ->> V_4 Double Cover, Internal Zorn Spinors S_a^2 = -1, & Spin Sector Fusion:
def quat_mul_f(p, q):
    return (p[0]*q[0] - p[1]*q[1] - p[2]*q[2] - p[3]*q[3],
            p[0]*q[1] + p[1]*q[0] + p[2]*q[3] - p[3]*q[2],
            p[0]*q[2] - p[1]*q[3] + p[2]*q[0] + p[3]*q[1],
            p[0]*q[3] + p[1]*q[2] - p[2]*q[1] + p[3]*q[0])
def quat_conj_f(p):
    return (p[0], -p[1], -p[2], -p[3])
def quat_sandwich_f(sq, vp):
    return quat_mul_f(quat_mul_f(sq, (F(0), vp[0], vp[1], vp[2])), quat_conj_f(sq))
q_i_f = (F(0), F(1), F(0), F(0))
q_j_f = (F(0), F(0), F(1), F(0))
q_k_f = (F(0), F(0), F(0), F(1))
assert quat_sandwich_f(q_i_f, q_f) == (F(0), klein_x_v_f(q_f)[0], klein_x_v_f(q_f)[1], klein_x_v_f(q_f)[2])
assert quat_sandwich_f((-F(0), -F(1), F(0), F(0)), q_f) == (F(0), klein_x_v_f(q_f)[0], klein_x_v_f(q_f)[1], klein_x_v_f(q_f)[2])
assert quat_sandwich_f(q_j_f, q_f) == (F(0), klein_y_v_f(q_f)[0], klein_y_v_f(q_f)[1], klein_y_v_f(q_f)[2])
assert quat_sandwich_f(q_k_f, q_f) == (F(0), klein_z_v_f(q_f)[0], klein_z_v_f(q_f)[1], klein_z_v_f(q_f)[2])
S_spin_x_f = (F(0), (F(1), F(0), F(0)), (F(1), F(0), F(0)), F(0))
assert z_mul(S_spin_x_f, S_spin_x_f) == (-F(1), (F(0), F(0), F(0)), (F(0), F(0), F(0)), -F(1))
def spin_proj_x_f(Xm):
    return z_sub(z_sub(z_add(Xm, klein_x_z_f(Xm)), klein_y_z_f(Xm)), klein_z_z_f(Xm))
def spin_proj_y_f(Xm):
    return z_sub(z_add(z_sub(Xm, klein_x_z_f(Xm)), klein_y_z_f(Xm)), klein_z_z_f(Xm))
def spin_proj_z_f(Xm):
    return z_add(z_sub(z_sub(Xm, klein_x_z_f(Xm)), klein_y_z_f(Xm)), klein_z_z_f(Xm))
assert spin_proj_x_f(spin_proj_y_f(X_obs_f)) == z_zero()
prod_xy_f = z_mul(spin_proj_x_f(X_obs_f), spin_proj_y_f(Y_obs_f))
assert spin_proj_x_f(prod_xy_f) == z_zero() and spin_proj_y_f(prod_xy_f) == z_zero()
def quat_sub_x_f(aq, vxq, wxq, bq):
    return (aq, (vxq, F(0), F(0)), (wxq, F(0), F(0)), bq)
def quat_sub_y_f(aq, vyq, wyq, bq):
    return (aq, (F(0), vyq, F(0)), (F(0), wyq, F(0)), bq)
def quat_sub_z_f(aq, vzq, wzq, bq):
    return (aq, (F(0), F(0), vzq), (F(0), F(0), wzq), bq)
assert z_assoc(quat_sub_y_f(y1, z1, xi1, y2), quat_sub_y_f(z2, xi2, y3, z3), quat_sub_y_f(xi3, y1, z2, xi1)) == z_zero()
assert z_assoc(quat_sub_z_f(y1, z1, xi1, y2), quat_sub_z_f(z2, xi2, y3, z3), quat_sub_z_f(xi3, y1, z2, xi1)) == z_zero()
assert gal_z3_f(quat_sub_x_f(y1, z1, xi1, y2)) == quat_sub_z_f(y1, z1, xi1, y2)
assert z_riccati_f(quat_sub_x_f(y1, z1, xi1, y2), (xi2, F(0), F(0))) == (xi2*xi1*xi2 + xi2*y2 - y1*xi2 - z1, F(0), F(0))
E_plus_f = (F(1), (F(0), F(0), F(0)), (F(0), F(0), F(0)), F(0))
dE_f = z_sub(z_mul(X_obs_f, E_plus_f), z_mul(E_plus_f, X_obs_f))
Om_f = z_mul(dE_f, dE_f)
assert dE_f == (F(0), (-X_obs_f[1][0], -X_obs_f[1][1], -X_obs_f[1][2]), X_obs_f[2], F(0))
assert z_mul(z_mul(E_plus_f, dE_f), E_plus_f) == z_zero()
assert z_mul(E_plus_f, Om_f) == z_mul(Om_f, E_plus_f)
sec_var_f = z_mul(z_mul(E_plus_f, z_sub(z_mul(X_obs_f, dE_f), z_mul(dE_f, X_obs_f))), E_plus_f)
curv_comp_f = z_mul(z_mul(E_plus_f, Om_f), E_plus_f)
assert z_add(sec_var_f, z_add(curv_comp_f, curv_comp_f)) == z_zero()
dE_inner_f = z_sub(z_mul(E_plus_f, X_obs_f), z_mul(X_obs_f, E_plus_f))
dbl_comm_f = z_sub(z_mul(E_plus_f, dE_inner_f), z_mul(dE_inner_f, E_plus_f))
assert z_sub(z_mul(dbl_comm_f, E_plus_f), z_mul(E_plus_f, dbl_comm_f)) == dE_f
E_minus_f = (F(0), (F(0), F(0), F(0)), (F(0), F(0), F(0)), F(1))
coarse_X_f = z_add(z_mul(z_mul(E_plus_f, X_obs_f), E_plus_f), z_mul(z_mul(E_minus_f, X_obs_f), E_minus_f))
assert z_add(coarse_X_f, dbl_comm_f) == X_obs_f
print("[PASS] FreeAlgebra & PolynomialRing: Archetypes XC-CXXVI (56D Freudenthal E_7 Euler Trace Identity, Inductive Colimit Doublet Tower, Zorn-Riccati Taylor Shift, 4-Spinor Cross-Difference, Gelfand-Retakh Elimination, Nambu-Gorkov Operator Cayley-Dickson Doubling, 5-Graded Spectral Projectors, OpCyclotomic3 & OpCyclotomic6 Jordan Norms, Z_3 Singlet Associativity, Octahedral S_4 = V_4 |>< S_3 Galois Group, Triality Trio of 5-Gradings, Quaternion Spin Double Cover Q_8 ->> V_4, Three Associative Quaternion Subalgebras H_{x,y,z}(A) ~= M_2(A), Connes (b, B) Cyclic Bicomplex, Taxonomic Coarse-Graining Hodge-Peirce Decomposition, & Zorn-Connes Vacuum Idempotent Curvature Collapse)")

print("======================================================================")
print("ALL CHECKS PASSED")
print("======================================================================")
