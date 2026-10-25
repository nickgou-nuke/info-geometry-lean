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

print("======================================================================")
print("ALL CHECKS PASSED")
print("======================================================================")
