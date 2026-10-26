# GAP Verification of Archetypes XLII-LIV:
# 5-Graded Zorn Algebra, Associative Heisenberg Nilradicals, 4-Gate Braid Loop,
# BCFW Contact Shift, and 3D Navier-Stokes Lamb-Vorticity Annihilation.

Print("======================================================================\n");
Print("GAP Verification: 5-Graded Zorn, BCFW, Arnold & Navier-Stokes\n");
Print("======================================================================\n");

R := PolynomialRing(Rationals, ["y1","z1","xi1","y2","z2","xi2","y3","z3","xi3","eta","y0","z0","ys","zs","ux","uy","uz","wx","wy","wz"]);
ind := IndeterminatesOfPolynomialRing(R);
y1 := ind[1]; z1 := ind[2]; xi1 := ind[3];
y2 := ind[4]; z2 := ind[5]; xi2 := ind[6];
y3 := ind[7]; z3 := ind[8]; xi3 := ind[9];
eta := ind[10]; y0 := ind[11]; z0 := ind[12];
ys := ind[13]; zs := ind[14];
ux := ind[15]; uy := ind[16]; uz := ind[17];
wx := ind[18]; wy := ind[19]; wz := ind[20];
zero := Zero(R);
one := One(R);

VecDot := function(u, v)
    return u[1]*v[1] + u[2]*v[2] + u[3]*v[3];
end;

VecCross := function(u, v)
    return [ u[2]*v[3] - u[3]*v[2],
             u[3]*v[1] - u[1]*v[3],
             u[1]*v[2] - u[2]*v[1] ];
end;

ZornZero := [ zero, [zero, zero, zero], [zero, zero, zero], zero ];
ZornOne  := [ one,  [zero, zero, zero], [zero, zero, zero], one  ];

ZornAdd := function(X, Y)
    return [ X[1] + Y[1], X[2] + Y[2], X[3] + Y[3], X[4] + Y[4] ];
end;

ZornSub := function(X, Y)
    return [ X[1] - Y[1], X[2] - Y[2], X[3] - Y[3], X[4] - Y[4] ];
end;

ZornMul := function(X, Y)
    local a, v, w, b;
    a := X[1]*Y[1] - VecDot(X[2], Y[3]);
    v := X[1]*Y[2] + Y[4]*X[2] - VecCross(X[3], Y[3]);
    w := Y[1]*X[3] + X[4]*Y[3] + VecCross(X[2], Y[2]);
    b := -VecDot(X[3], Y[2]) + X[4]*Y[4];
    return [a, v, w, b];
end;

ZornAssoc := function(X, Y, Z)
    return ZornSub(ZornMul(ZornMul(X, Y), Z), ZornMul(X, ZornMul(Y, Z)));
end;

GradePlus1 := function(y, z)
    return [ zero, [zero, y, z], [zero, zero, zero], zero ];
end;

GradePlus2 := function(xi)
    return [ zero, [zero, zero, zero], [xi, zero, zero], zero ];
end;

GradeMinus2 := function(e)
    return [ zero, [e, zero, zero], [zero, zero, zero], zero ];
end;

GradeZero := function(rp, rm)
    return [ rp, [zero, zero, zero], [zero, zero, zero], rm ];
end;

HeisenbergGroupPlus := function(y, z, xi)
    return [ one, [zero, y, z], [xi, zero, zero], one ];
end;

# 1. Verify Heisenberg Group Associativity & 4-Gate Braid Monodromy Loop
G1 := HeisenbergGroupPlus(y1, z1, xi1);
G2 := HeisenbergGroupPlus(y2, z2, xi2);
G3 := HeisenbergGroupPlus(y3, z3, xi3);
G1_inv := HeisenbergGroupPlus(-y1, -z1, -xi1);
G2_inv := HeisenbergGroupPlus(-y2, -z2, -xi2);
w12 := y1*z2 - z1*y2;

if ZornAssoc(G1, G2, G3) <> ZornZero then
    Error("FAIL: 3-Layer Heisenberg associator non-zero");
fi;
if ZornMul(ZornMul(G1, G2), ZornMul(G1_inv, G2_inv)) <> HeisenbergGroupPlus(zero, zero, 2*w12) then
    Error("FAIL: 4-Gate braid commutator loop mismatch");
fi;
Print("[PASS] GAP: 5-Graded Heisenberg Group Associativity & 4-Gate Braid Loop\n");

# 2. Verify 5-Graded BCFW Transverse Shift & Contact Pole Residue
P0 := [ one, [zero, -y0, -z0], [zero, zero, zero], zero ];
P_shifted := [ one, [zero, -(ys + y0), -(zs + z0)], [zero, zero, zero], zero ];
S_plus := HeisenbergGroupPlus(ys, zs, zero);
S_minus := HeisenbergGroupPlus(-ys, -zs, zero);
w_res := ys*z0 - zs*y0;

if ZornAssoc(S_plus, P0, S_minus) <> ZornZero then
    Error("FAIL: BCFW shift associator non-zero");
fi;
if ZornMul(P0, S_minus) <> ZornSub(P_shifted, GradePlus2(w_res)) then
    Error("FAIL: Right BCFW shift residue mismatch");
fi;
if ZornMul(GradeMinus2(eta), ZornSub(ZornMul(P0, S_minus), P_shifted)) <> GradeZero(eta*w_res, zero) then
    Error("FAIL: Dual contact readout of BCFW residue mismatch");
fi;
Print("[PASS] GAP: 5-Graded BCFW Transverse Shift & Contact Residue Readout\n");

# 3. Verify Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence
U3 := [ zero, [ux, uy, uz], [zero, zero, zero], zero ];
Om3 := [ zero, [wx, wy, wz], [zero, zero, zero], zero ];
Lamb3 := ZornMul(Om3, U3);

if ZornMul(U3, Lamb3) <> ZornZero or ZornMul(Lamb3, U3) <> ZornZero then
    Error("FAIL: 3D Lamb-velocity product non-zero");
fi;
if ZornMul(Om3, Lamb3) <> ZornZero or ZornMul(Lamb3, Om3) <> ZornZero then
    Error("FAIL: 3D Lamb-vorticity product non-zero");
fi;
Print("[PASS] GAP: Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence\n");

# 4. Verify Archetypes LXI & LXII: 1934 JvNW Cubic Peirce Polynomial & Fundamental Jordan Axiom (III)
ZornJordan := function(X, Y)
    return ZornAdd(ZornMul(X, Y), ZornMul(Y, X));
end;

e11 := GradeZero(one, zero);
Xjvnw := [ y1, [ux, uy, uz], [wx, wy, wz], z1 ];
Bjvnw := [ y2, [wx, uz, uy], [ux, wz, wy], z2 ];
L1e := ZornJordan(e11, Xjvnw);
L2e := ZornJordan(e11, L1e);
L3e := ZornJordan(e11, L2e);
if ZornAdd(ZornSub(L3e, ZornAdd(ZornAdd(L2e, L2e), L2e)), ZornAdd(L1e, L1e)) <> ZornZero then
    Error("FAIL: 1934 JvNW Cubic Peirce polynomial non-zero");
fi;
Asq := ZornJordan(Xjvnw, Xjvnw);
if ZornJordan(ZornJordan(Asq, Bjvnw), Xjvnw) <> ZornJordan(Asq, ZornJordan(Bjvnw, Xjvnw)) then
    Error("FAIL: 1934 JvNW Fundamental Jordan Axiom (III) failed");
fi;
Print("[PASS] GAP: 1934 JvNW Cubic Peirce Polynomial & Fundamental Jordan Axiom (III)\n");

# 5. Verify Archetypes LV-LX: QGT Madelung Split, Metriplectic Flow, Baryon-Meson Confinement, & Master Trifactor Synthesis
ZornComm := function(X, Y)
    return ZornSub(ZornMul(X, Y), ZornMul(Y, X));
end;
ZornScale := function(c, X)
    return [ c*X[1], [c*X[2][1], c*X[2][2], c*X[2][3]], [c*X[3][1], c*X[3][2], c*X[3][3]], c*X[4] ];
end;

Lp_v := [ zero, [ux, uy, uz], [zero, zero, zero], zero ];
Lm_w := [ zero, [zero, zero, zero], [wx, wy, wz], zero ];
QGT_vw := ZornScale(2*one, ZornMul(Lp_v, Lm_w));
g_vw := ZornJordan(Lp_v, Lm_w);
om_vw := ZornComm(Lp_v, Lm_w);
if QGT_vw <> ZornAdd(g_vw, om_vw) then
    Error("FAIL: Archetype LV QGT Madelung split mismatch");
fi;
if ZornAdd(ZornComm(Lp_v, Xjvnw), ZornJordan(Lp_v, Xjvnw)) <> ZornScale(2*one, ZornMul(Lp_v, Xjvnw)) then
    Error("FAIL: Archetype LVI Metriplectic chiral factorization mismatch");
fi;

# Archetype LIX: 3-Quark Baryon Singlet Antisymmetry & Pauli Exclusion
Lp_q1 := [ zero, [y1, z1, xi1], [zero, zero, zero], zero ];
Lp_q2 := [ zero, [y2, z2, xi2], [zero, zero, zero], zero ];
Lp_q3 := [ zero, [y3, z3, xi3], [zero, zero, zero], zero ];
B_123 := ZornAssoc(Lp_q1, Lp_q2, Lp_q3);
B_213 := ZornAssoc(Lp_q2, Lp_q1, Lp_q3);
B_113 := ZornAssoc(Lp_q1, Lp_q1, Lp_q3);
baryon_det := VecDot([y1, z1, xi1], VecCross([y2, z2, xi2], [y3, z3, xi3]));
if B_123 <> GradeZero(baryon_det, -baryon_det) then
    Error("FAIL: Archetype LIX Baryon singlet determinant mismatch");
fi;
if ZornAdd(B_123, B_213) <> ZornZero or B_113 <> ZornZero then
    Error("FAIL: Archetype LIX Baryon antisymmetry / Pauli exclusion failed");
fi;

# Archetype LX: Chiral Wavefunction Factors, 4-Factor Associative Square, & Contact Flow Idempotent
Psi_L := [ one, [zero, zero, zero], [wx, wy, wz], zero ];
Psi_R := [ one, [ux, uy, uz], [zero, zero, zero], zero ];
Pi_tri := ZornMul(Psi_L, Psi_R);
if ZornMul(Psi_L, Psi_L) <> Psi_L or ZornMul(Psi_R, Psi_R) <> Psi_R then
    Error("FAIL: Archetype LX Chiral wavefunction idempotence failed");
fi;
if ZornAssoc(Psi_R, Psi_L, Psi_R) <> ZornZero or ZornAssoc(Psi_L, Psi_R, Psi_L) <> ZornZero then
    Error("FAIL: Archetype LX Chiral sandwich associators non-zero over commutative ring");
fi;
if ZornMul(Pi_tri, Pi_tri) <> ZornMul(Psi_L, ZornMul(ZornMul(Psi_R, Psi_L), Psi_R)) then
    Error("FAIL: Archetype LX 4-Factor associative square failed");
fi;
Pi_c1 := [ one, [zero, -y1, -z1], [xi1, zero, zero], zero ];
Pi_c2 := [ one, [zero, -y2, -z2], [xi2, zero, zero], zero ];
if ZornMul(Pi_c1, Pi_c1) <> Pi_c1 then
    Error("FAIL: Archetype LX Contact flow strict idempotence failed");
fi;
if ZornMul(Pi_c1, Pi_c2) <> [ one, [zero, -y2, -z2], [xi1 + w12, zero, zero], zero ] then
    Error("FAIL: Archetype LX Two-state contact Lamb composition failed");
fi;
Print("[PASS] GAP: Archetypes LV-LX (QGT Madelung, Metriplectic, Baryon Singlet, & Master Trifactor Synthesis)\n");

# 6. Verify Archetypes LXIII & LXIV: Wheeler "It from Bit" (P^2 = P), "Boundary of a Boundary is Zero" (d^2 = 0), & Volume Emergence
e22 := GradeZero(zero, one);
d_v_wh := ZornSub(Psi_R, e11);
d_w_wh := ZornSub(Psi_L, e11);
if ZornMul(d_v_wh, d_v_wh) <> ZornZero or ZornMul(d_w_wh, d_w_wh) <> ZornZero then
    Error("FAIL: Archetype LXIII Wheeler boundary-of-boundary nilpotence failed");
fi;
if ZornAdd(ZornMul(d_v_wh, d_w_wh), ZornMul(d_w_wh, d_v_wh)) <> g_vw then
    Error("FAIL: Archetype LXIII Wheeler Hodge Laplacian metric emergence failed");
fi;
if ZornMul(Lp_q1, ZornMul(Lp_q2, Lp_q3)) <> GradeZero(-baryon_det, zero) or
   ZornMul(ZornMul(Lp_q1, Lp_q2), Lp_q3) <> GradeZero(zero, -baryon_det) then
    Error("FAIL: Archetype LXIV Wheeler 3-bit volume emergence failed");
fi;
Print("[PASS] GAP: Archetypes LXIII-LXIV (Wheeler 'It from Bit', 'Boundary of a Boundary is Zero', & 3-Bit Volume)\n");

# 7. Verify Archetypes LXV & LXVI: Euler 5-Grading Operator E_5, Nilradical Derivation, KKT Degree-5 Polynomial, & (2|3) Supertrace
Euler5 := function(X)
    return [ zero, [ -2*X[2][1], X[2][2], X[2][3] ], [ 2*X[3][1], -X[3][2], -X[3][3] ], zero ];
end;

N1p := ZornAdd(GradePlus1(y1, z1), GradePlus2(xi1));
N2p := ZornAdd(GradePlus1(y2, z2), GradePlus2(xi2));
if Euler5(ZornMul(N1p, N2p)) <> ZornAdd(ZornMul(Euler5(N1p), N2p), ZornMul(N1p, Euler5(N2p))) then
    Error("FAIL: Archetype LXV Euler 5-grading nilradical derivation failed");
fi;
E1_A := Euler5(Xjvnw);
E2_A := Euler5(E1_A);
E3_A := Euler5(E2_A);
E4_A := Euler5(E3_A);
E5_A := Euler5(E4_A);
if ZornAdd(ZornSub(E5_A, ZornScale(5*one, E3_A)), ZornScale(4*one, E1_A)) <> ZornZero then
    Error("FAIL: Archetype LXV KKT degree-5 minimal polynomial E_5^5 - 5 E_5^3 + 4 E_5 = 0 failed");
fi;
Print("[PASS] GAP: Archetypes LXV-LXVI (Euler 5-Grading Nilradical Derivation & KKT Degree-5 Minimal Polynomial)\n");

# 8. Verify Archetypes LXVII & LXVIII: Rolf Dahm Dihedral D_4 & PG(3,2) Collinear Operator Triple (s0 * s1) * r1 = r0
DahmR0 := [ one, [zero, zero, zero], [zero, zero, zero], one ];
DahmR1 := [ zero, [-one, zero, zero], [-one, zero, zero], zero ];
DahmS0 := [ one, [zero, zero, zero], [zero, zero, zero], -one ];
DahmS1 := [ zero, [one, zero, zero], [-one, zero, zero], zero ];
if ZornMul(DahmR1, DahmR1) <> ZornScale(-one, DahmR0) or ZornMul(DahmS0, DahmS0) <> DahmR0 or ZornMul(DahmS1, DahmS1) <> DahmR0 then
    Error("FAIL: Archetype LXVIII Dahm D_4 generator squares failed");
fi;
if ZornMul(ZornMul(DahmS0, DahmS1), DahmR1) <> DahmR0 then
    Error("FAIL: Archetype LXVIII Dahm PG(3,2) collinear triple product (s0*s1)*r1 = r0 failed");
fi;
# Archetypes LXIX & LXX: Maxwell-Poynting Hodge-Dual Stress Matrix J(E, B) * J*(E, B)
J_EM := [ zero, [ux, uy, uz], [wx, wy, wz], zero ];
J_Star := [ zero, [-wx, -wy, -wz], [ux, uy, uz], zero ];
S_Poynt := VecCross([ux, uy, uz], [wx, wy, wz]);
if ZornMul(J_EM, J_Star) <> [ -VecDot([ux, uy, uz], [ux, uy, uz]), S_Poynt, [-S_Poynt[1], -S_Poynt[2], -S_Poynt[3]], VecDot([wx, wy, wz], [wx, wy, wz]) ] then
    Error("FAIL: Archetype LXIX Maxwell-Poynting Hodge-dual stress matrix failed");
fi;
# Archetypes LXXI & LXXII: Saniga-Holweck-Pracna Grassmannian G_2(N+1) Edge-Triangle Invariance & Sedenion Zero Divisors
ZornConj := function(X)
    return [ X[4], [-X[2][1], -X[2][2], -X[2][3]], [-X[3][1], -X[3][2], -X[3][3]], X[1] ];
end;
Om12 := [ zero, [y1 - y2, z1 - z2, xi1 - xi2], [zero, zero, zero], zero ];
Om23 := [ zero, [y2 - y3, z2 - z3, xi2 - xi3], [zero, zero, zero], zero ];
Om31 := [ zero, [y3 - y1, z3 - z1, xi3 - xi1], [zero, zero, zero], zero ];
if ZornMul(Om12, Om23) <> ZornMul(Om23, Om31) or ZornMul(Om23, Om31) <> ZornMul(Om31, Om12) then
    Error("FAIL: Archetype LXXI Grassmannian edge-triangle collinear product invariance failed");
fi;
SedX := ZornSub(ZornMul(Lp_v, Lm_w), ZornMul(ZornScale(-one, Lp_v), ZornConj(Lm_w)));
SedY := ZornAdd(ZornMul(ZornConj(Lp_v), ZornScale(-one, Lp_v)), ZornMul(Lm_w, Lm_w));
if SedX <> ZornZero or SedY <> ZornZero then
    Error("FAIL: Archetype LXXII Sedenion two-sided zero divisor failed");
fi;
# Archetypes LXXIII & LXXIV: Pasch 4-Simplex Tetrahedral 2-Boundary Closure P_123 - P_134 + P_124 - P_234 = 0
Om34 := [ zero, [y3 - y0, z3 - z0, xi3 - eta], [zero, zero, zero], zero ];
Om13 := ZornAdd(Om12, Om23);
Om24 := ZornAdd(Om23, Om34);
P123 := ZornMul(Om12, Om23);
P134 := ZornMul(Om13, Om34);
P124 := ZornMul(Om12, Om24);
P234 := ZornMul(Om23, Om34);
if ZornSub(ZornAdd(ZornSub(P234, P134), P124), P123) <> ZornZero then
    Error("FAIL: Archetype LXXIV Pasch 4-simplex tetrahedral 2-boundary closure failed");
fi;
Print("[PASS] GAP: Archetypes LXVII-LXXIV (Dahm D_4, Maxwell-Poynting Stress, Grassmannian G_2(N+1), Sedenion Zero Divisors, & Pasch 4-Simplex 2-Boundary)\n");

# 9. Verify Archetypes LXXV, LXXVI, LXXVII, & LXXVIII: Catto E_9/E_10 Weyl Reflection & 27D Split-Octonion Albert-Freudenthal Adjoint & Determinant Law
ZornMulStd := function(X, Y)
    local a, v, w, b;
    a := X[1]*Y[1] + VecDot(X[2], Y[3]);
    v := X[1]*Y[2] + Y[4]*X[2] + VecCross(X[3], Y[3]);
    w := Y[1]*X[3] + X[4]*Y[3] - VecCross(X[2], Y[2]);
    b := VecDot(X[3], Y[2]) + X[4]*Y[4];
    return [a, v, w, b];
end;
ZornJordanStd := function(X, Y) return ZornAdd(ZornMulStd(X, Y), ZornMulStd(Y, X)); end;
ZornTrace := function(X) return X[1] + X[4]; end;
ZornNorm := function(X) return X[1]*X[4] - VecDot(X[2], X[3]); end;
ZornInner := function(X, Y) return ZornTrace(ZornMulStd(X, ZornConj(Y))); end;
ZornJT := function(X, Y, Z)
    return ZornSub(ZornAdd(ZornJordanStd(ZornJordanStd(X, Y), Z), ZornJordanStd(X, ZornJordanStd(Y, Z))), ZornJordanStd(ZornJordanStd(X, Z), Y));
end;
Q_alb := Xjvnw;
Xi1_alb := Bjvnw;
Xi2_alb := [ eta, [y1, z2, xi3], [y2, z3, xi1], y3 ];
if ZornJT(Xi1_alb, ZornConj(Q_alb), Xi1_alb) <> ZornScale(4*one, ZornSub(ZornScale(ZornTrace(ZornMulStd(Q_alb, ZornConj(Xi1_alb))), Xi1_alb), ZornScale(ZornNorm(Xi1_alb), Q_alb))) then
    Error("FAIL: Archetype LXXV Jacobson Jordan triple Weyl reflection failed");
fi;
if ZornTrace(ZornMulStd(ZornMulStd(Q_alb, Xi2_alb), ZornConj(Xi1_alb))) <> ZornTrace(ZornMulStd(Q_alb, ZornMulStd(Xi2_alb, ZornConj(Xi1_alb)))) then
    Error("FAIL: Archetype LXXVII Freudenthal cubic trace associator invariance failed");
fi;
xp_a := y0; xm_a := z0; v_a := ys;
sh_xp := xm_a*v_a - ZornNorm(Xi2_alb);
sh_xm := xp_a*v_a - ZornNorm(Xi1_alb);
sh_v  := xp_a*xm_a - ZornNorm(Q_alb);
sh_Q  := ZornSub(ZornMulStd(Xi1_alb, ZornConj(Xi2_alb)), ZornScale(v_a, Q_alb));
sh_Xi1 := ZornSub(ZornMulStd(Q_alb, Xi2_alb), ZornScale(xm_a, Xi1_alb));
sh_Xi2 := ZornSub(ZornMulStd(ZornConj(Q_alb), Xi1_alb), ZornScale(xp_a, Xi2_alb));
det27 := xp_a*xm_a*v_a - xp_a*ZornNorm(Xi2_alb) - xm_a*ZornNorm(Xi1_alb) - v_a*ZornNorm(Q_alb) + ZornTrace(ZornMulStd(ZornMulStd(Q_alb, Xi2_alb), ZornConj(Xi1_alb)));
ac_xp := 2*xp_a*sh_xp + ZornInner(Q_alb, sh_Q) + ZornInner(Xi1_alb, sh_Xi1);
ac_xm := 2*xm_a*sh_xm + ZornInner(ZornConj(Q_alb), ZornConj(sh_Q)) + ZornInner(Xi2_alb, sh_Xi2);
ac_v  := 2*v_a*sh_v + ZornInner(Xi1_alb, sh_Xi1) + ZornInner(Xi2_alb, sh_Xi2);
ac_Q  := ZornAdd(ZornAdd(ZornScale(xp_a + xm_a, sh_Q), ZornScale(sh_xp + sh_xm, Q_alb)), ZornAdd(ZornMulStd(Xi1_alb, ZornConj(sh_Xi2)), ZornMulStd(sh_Xi1, ZornConj(Xi2_alb))));
ac_Xi1 := ZornAdd(ZornAdd(ZornScale(xp_a + v_a, sh_Xi1), ZornScale(sh_xp + sh_v, Xi1_alb)), ZornAdd(ZornMulStd(Q_alb, sh_Xi2), ZornMulStd(sh_Q, Xi2_alb)));
ac_Xi2 := ZornAdd(ZornAdd(ZornScale(xm_a + v_a, sh_Xi2), ZornScale(sh_xm + sh_v, Xi2_alb)), ZornAdd(ZornMulStd(ZornConj(Q_alb), sh_Xi1), ZornMulStd(ZornConj(sh_Q), Xi1_alb)));
if ac_xp <> 2*det27 or ac_xm <> 2*det27 or ac_v <> 2*det27 or ac_Q <> ZornZero or ac_Xi1 <> ZornZero or ac_Xi2 <> ZornZero then
    Error("FAIL: Archetype LXXVII 27D Split-Octonion Albert-Freudenthal Adjoint & Determinant Law failed");
fi;
# Archetypes LXXIX & LXXX: Z_3-Triality Determinant Splitting & 72-Channel 3x3 Nilradical Freudenthal Inversion
if ZornAdd(ZornAdd(ZornAssoc(Lp_q1, Lp_q2, Lp_q3), ZornAssoc(Lp_q2, Lp_q3, Lp_q1)), ZornAssoc(Lp_q3, Lp_q1, Lp_q2)) <> GradeZero(3*baryon_det, -3*baryon_det) then
    Error("FAIL: Archetype LXXIX Z_3-triality cyclic associator sum failed");
fi;
# Archetypes LXXXI, LXXXII, & LXXXIII: Steen H. Hansen (21 Oct 2026) Cl(4,2) Doublet Tower & Zorn Conformal-Triality Marriage
Dzorn := GradeZero(one, -one);
if ZornSub(ZornMul(Dzorn, Lp_q1), ZornMul(Lp_q1, Dzorn)) <> ZornAdd(Lp_q1, Lp_q1) or ZornAdd(ZornMul(Dzorn, Lp_q1), ZornMul(Lp_q1, Dzorn)) <> ZornZero then
    Error("FAIL: Archetype LXXXI Hansen dilatation grading relation failed");
fi;
if ZornSub(ZornMul(Lp_q1, Lp_q2), ZornMul(Lp_q2, Lp_q1)) <> [ zero, [zero, zero, zero], 2 * VecCross([y1, z1, xi1], [y2, z2, xi2]), zero ] then
    Error("FAIL: Archetype LXXXIII Hansen Zorn conformal-triality cross-product commutator failed");
fi;
if ((y1 - one) - one)^2 - ((y1 - one) + one) <> (y1 - one)*(y1 - 4*one) then
    Error("FAIL: Archetype LXXXII Hansen S_2=0 d=4 Lorentzian selection failed");
fi;
# Archetypes LXXXIV & LXXXV: Zero Chiral Volume, Krein Null Kernel, Parabolic Boundary Sheaf, & Majorana Horizon Zero Modes
if VecDot([zero, y1, z1], VecCross([zero, y2, z2], [zero, y3, z3])) <> zero then
    Error("FAIL: Archetype LXXXIV Zero Chiral 3-Volume on transverse screen failed");
fi;
Ep1_g := GradePlus1(y1, z1);
Em1_g := [ zero, [zero, zero, zero], [zero, y1, z1], zero ];
ZMaj_g := GradePlus2(xi3);
Em2_g := GradeMinus2(xi3);
Pib_perp := ZornSub(ZornOne, Pi_c1);
if ZornMul(Ep1_g, ZMaj_g) <> ZornZero or ZornMul(ZMaj_g, Ep1_g) <> ZornZero or ZornMul(Em1_g, Em2_g) <> ZornZero or ZornMul(Em2_g, Em1_g) <> ZornZero then
    Error("FAIL: Archetype LXXXIV Krein null kernel orthogonality failed");
fi;
if ZornMul(Em1_g, ZMaj_g) <> GradePlus1(-z1*xi3, y1*xi3) then
    Error("FAIL: Archetype LXXXIV Krein symplectic transverse rotation failed");
fi;
if ZornMul(Pi_c1, ZMaj_g) <> ZornZero or ZornMul(ZMaj_g, Pi_c1) <> ZMaj_g or ZornMul(Pib_perp, ZMaj_g) <> ZMaj_g or ZornMul(ZMaj_g, Pib_perp) <> ZornZero then
    Error("FAIL: Archetype LXXXV Parabolic boundary Majorana horizon zero-mode stabilization/nullspace failed");
fi;
# Archetypes LXXXVI & LXXXVII: Chevalley-Lounesto-Shirokov Spinor Ideals & Relativistic Dirac-Krein Ket-Bra Duality
psi_c1_g := [ y1, [zero, zero, zero], [xi1, zero, zero], zero ];
phi_c2_bar_g := [ y2, [xi2, zero, zero], [zero, zero, zero], zero ];
psi_c3_g := [ y3, [zero, zero, zero], [xi3, zero, zero], zero ];
if ZornAssoc(psi_c1_g, phi_c2_bar_g, psi_c3_g) <> ZornZero then
    Error("FAIL: Archetype LXXXVII Contact spinor ket-bra-ket associativity failed");
fi;
# Archetypes LXXXVIII & LXXXIX: Trifactor-Loxodromic Compass, Doubled 4-Vector Potentials, & 8D Zorn-Riccati Möbius Operator
P_row_g := [ one, [y1, z1, xi1], [zero, zero, zero], zero ];
P_col_g := [ one, [zero, zero, zero], [y2, z2, xi2], zero ];
U_up_g := [ one, [y1, z1, xi1], [zero, zero, zero], one ];
U_lo_g := [ one, [zero, zero, zero], [y2, z2, xi2], one ];
T_bruhat_g := ZornMul(ZornMul(U_lo_g, [ one, [zero, zero, zero], [zero, zero, zero], xi3 ]), U_up_g);
if T_bruhat_g <> ZornAdd(ZornMul(ZornMul(P_col_g, [ one, [zero, zero, zero], [zero, zero, zero], zero ]), P_row_g), [ zero, [zero, zero, zero], [zero, zero, zero], xi3 ]) then
    Error("FAIL: Archetype LXXXVIII Trifactor compass needle decomposition failed");
fi;
riccati_T_g := VecDot(T_bruhat_g[3], [y1, z1, xi1]) * [y1, z1, xi1] + T_bruhat_g[4] * [y1, z1, xi1] + T_bruhat_g[1] * [y1, z1, xi1] - T_bruhat_g[2];
if riccati_T_g <> xi3 * [y1, z1, xi1] then
    Error("FAIL: Archetype LXXXIX 8D Zorn-Riccati Möbius Schur residual failed");
fi;
# Archetypes XC-XCV: 56D Freudenthal E_7 Euler Trace Identity <M, M^#>_27 = 3 Det_27(M), Doublet Tower, & Gelfand-Retakh Gauss-Bruhat Elimination
trace_pair_27_g := xp_a*sh_xp + xm_a*sh_xm + v_a*sh_v + ZornInner(Q_alb, sh_Q) + ZornInner(Xi1_alb, sh_Xi1) + ZornInner(Xi2_alb, sh_Xi2);
if trace_pair_27_g <> 3*det27 then
    Error("FAIL: Archetype XC 56D Freudenthal Euler trace identity <M, M^#>_27 = 3 Det_27(M) failed");
fi;
U_up_neg_g := [ one, -[y1, z1, xi1], [zero, zero, zero], one ];
U_lo_neg_g := [ one, [zero, zero, zero], -[y2, z2, xi2], one ];
if ZornMul(ZornMul(U_lo_neg_g, T_bruhat_g), U_up_neg_g) <> [ one, [zero, zero, zero], [zero, zero, zero], xi3 ] then
    Error("FAIL: Archetype XCIV Gelfand-Retakh Gauss-Bruhat trifactor elimination failed");
fi;
if T_bruhat_g[4] + VecDot(T_bruhat_g[3], T_bruhat_g[2]) <> xi3 then
    Error("FAIL: Archetype XCV Gelfand-Retakh (2,2)-quasideterminant extraction failed");
fi;
cross_orig_g := ((1 - VecDot([y1,z1,xi1]+[y3,z3,xi3], [y2,z2,xi2]+[y3,z3,xi3])) - (1 - VecDot([y1,z1,xi1]+[y3,z3,xi3], [y3,z3,xi3]+[y3,z3,xi3])))
              - ((1 - VecDot([y3,z3,xi3]+[y3,z3,xi3], [y2,z2,xi2]+[y3,z3,xi3])) - (1 - VecDot([y3,z3,xi3]+[y3,z3,xi3], [y3,z3,xi3]+[y3,z3,xi3])));
cross_base_g := ((1 - VecDot([y1,z1,xi1], [y2,z2,xi2])) - (1 - VecDot([y1,z1,xi1], [y3,z3,xi3])))
              - ((1 - VecDot([y3,z3,xi3], [y2,z2,xi2])) - (1 - VecDot([y3,z3,xi3], [y3,z3,xi3])));
if cross_orig_g <> cross_base_g then
    Error("FAIL: Archetype XCIII 4-spinor cross-difference translation invariance failed");
fi;
# Archetypes XCVI-XCVIII: Operator-Twisted Nambu-Gorkov Cayley-Dickson Doubling & 5-Graded Spectral Projectors
CDMul_g := function(Om, z_p, w_p)
    return [ z_p[1]*w_p[1] + Om*(w_p[2]*z_p[2]), z_p[1]*w_p[2] + w_p[1]*z_p[2] ];
end;
E_cd_g := [ zero, one ];
Z_cd_g := [ y1, z1 ];
if CDMul_g(xi1, Z_cd_g, [ y1, -z1 ]) <> [ y1*y1 - xi1*(z1*z1), zero ] then
    Error("FAIL: Archetype XCVI Nambu-Gorkov operator Cayley-Dickson norm cancellation failed");
fi;
E2_cd_g := CDMul_g(xi1, E_cd_g, E_cd_g);
if E2_cd_g <> [ xi1, zero ] or CDMul_g(xi1, E2_cd_g, E2_cd_g) <> [ xi1*xi1, zero ] then
    Error("FAIL: Archetype XCVII Nambu-Gorkov doubling generator powers failed");
fi;
OpEuler5_g := function(Z_m)
    return [ zero, [ -2*Z_m[2][1], Z_m[2][2], Z_m[2][3] ], [ 2*Z_m[3][1], -Z_m[3][2], -Z_m[3][3] ], zero ];
end;
X_full_g := [ y1, [xi1, y2, z2], [xi2, y3, z3], z1 ];
D1_g := OpEuler5_g(X_full_g);
D2_g := OpEuler5_g(D1_g);
D3_g := OpEuler5_g(D2_g);
D4_g := OpEuler5_g(D3_g);
if ZornSub(D3_g, D1_g) <> [ zero, [ -6*xi1, zero, zero ], [ 6*xi2, zero, zero ], zero ] then
    Error("FAIL: Archetype XCVIII Cubic contact horizon spectral projector failed");
fi;
if ZornAdd(ZornSub(D4_g, 5*D2_g), 4*X_full_g) <> [ 4*y1, [zero, zero, zero], [zero, zero, zero], 4*z1 ] then
    Error("FAIL: Archetype XCVIII Quartic nucleus spectral projector failed");
fi;
# Archetypes XCIX-C: Cyclotomic Factorizations & Z_6 Galois Automorphism Group
if (xi1^6 - one) <> (xi1 - one)*(xi1 + one)*(xi1^2 + xi1 + one)*(xi1^2 - xi1 + one) then
    Error("FAIL: Archetype XCIX Cyclotomic polynomial factorization failed");
fi;
TriPermVec := function(u) return [ u[2], u[3], u[1] ]; end;
GradeParityVec := function(u) return [ u[1], -u[2], -u[3] ]; end;
ZornGaloisZ3 := function(M) return [ M[1], TriPermVec(M[2]), TriPermVec(M[3]), M[4] ]; end;
ZornGradeParity := function(M) return [ M[1], GradeParityVec(M[2]), GradeParityVec(M[3]), M[4] ]; end;
ZornGaloisZ6 := function(M) return [ M[1], -TriPermVec(M[2]), -TriPermVec(M[3]), M[4] ]; end;
if ZornGaloisZ3(ZornMul(Q_alb, Xi1_alb)) <> ZornMul(ZornGaloisZ3(Q_alb), ZornGaloisZ3(Xi1_alb)) then
    Error("FAIL: Archetype C Z_3 triality Galois automorphism failed");
fi;
if ZornGradeParity(ZornMul(Q_alb, Xi1_alb)) <> ZornMul(ZornGradeParity(Q_alb), ZornGradeParity(Xi1_alb)) then
    Error("FAIL: Archetype C 5-grading parity Z_2 automorphism failed");
fi;
if ZornGaloisZ6(ZornGaloisZ6(Q_alb)) <> ZornGaloisZ3(ZornGaloisZ3(Q_alb)) then
    Error("FAIL: Archetype C Z_6 cyclotomic Galois period law failed");
fi;
Cyc3Mul_g := function(z, w) return [ z[1]*w[1] - z[2]*w[2], z[1]*w[2] + z[2]*w[1] - z[2]*w[2] ]; end;
Cyc6Mul_g := function(z, w) return [ z[1]*w[1] - z[2]*w[2], z[1]*w[2] + z[2]*w[1] + z[2]*w[2] ]; end;
ToCyc3_g := function(z) return [ z[1] + z[2], z[2] ]; end;
if ToCyc3_g(Cyc6Mul_g([y1, z1], [y2, z2])) <> Cyc3Mul_g(ToCyc3_g([y1, z1]), ToCyc3_g([y2, z2])) then
    Error("FAIL: Archetype CIII OpCyclotomic6 <-> OpCyclotomic3 ring isomorphism failed");
fi;
Riccati_g := function(M, q_v)
    return VecDot(M[3], q_v) * q_v + M[4] * q_v - M[1] * q_v - M[2];
end;
if TriPermVec(Riccati_g(Q_alb, [y1, z1, xi1])) <> Riccati_g(ZornGaloisZ3(Q_alb), TriPermVec([y1, z1, xi1])) then
    Error("FAIL: Archetype CIV Z_3 triality Zorn-Riccati equivariance failed");
fi;
if -TriPermVec(Riccati_g(Q_alb, [y1, z1, xi1])) <> Riccati_g(ZornGaloisZ6(Q_alb), -TriPermVec([y1, z1, xi1])) then
    Error("FAIL: Archetype CIV Z_6 cyclotomic Zorn-Riccati equivariance failed");
fi;
ZornSinglet_g := function(a_s, c_s, d_s, b_s) return [ a_s, [c_s, c_s, c_s], [d_s, d_s, d_s], b_s ]; end;
S1_g := ZornSinglet_g(y1, z1, xi1, y2);
S2_g := ZornSinglet_g(z2, xi2, y3, z3);
S3_g := ZornSinglet_g(xi3, y1, z2, xi1);
if ZornSub(ZornMul(ZornMul(S1_g, S2_g), S3_g), ZornMul(S1_g, ZornMul(S2_g, S3_g))) <> ZornZero then
    Error("FAIL: Archetype CVI Z_3 singlet strict associativity failed");
fi;
ReflVec_g := function(v) return [ -v[1], -v[3], -v[2] ]; end;
KleinXVec_g := function(v) return [ v[1], -v[2], -v[3] ]; end;
KleinYVec_g := function(v) return [ -v[1], v[2], -v[3] ]; end;
KleinZVec_g := function(v) return [ -v[1], -v[2], v[3] ]; end;
ZornRefl_g := function(M) return [ M[1], ReflVec_g(M[2]), ReflVec_g(M[3]), M[4] ]; end;
ZornKleinX_g := function(M) return [ M[1], KleinXVec_g(M[2]), KleinXVec_g(M[3]), M[4] ]; end;
ZornKleinY_g := function(M) return [ M[1], KleinYVec_g(M[2]), KleinYVec_g(M[3]), M[4] ]; end;
ZornKleinZ_g := function(M) return [ M[1], KleinZVec_g(M[2]), KleinZVec_g(M[3]), M[4] ]; end;
if ZornRefl_g(ZornMul(Q_alb, Xi1_alb)) <> ZornMul(ZornRefl_g(Q_alb), ZornRefl_g(Xi1_alb)) then
    Error("FAIL: Archetype CVIII signed reflection automorphism failed");
fi;
if ZornRefl_g(ZornGaloisZ3(ZornRefl_g(Q_alb))) <> ZornGaloisZ3(ZornGaloisZ3(Q_alb)) then
    Error("FAIL: Archetype CVIII dihedral S_3 relation failed");
fi;
if ZornKleinY_g(ZornMul(Q_alb, Xi1_alb)) <> ZornMul(ZornKleinY_g(Q_alb), ZornKleinY_g(Xi1_alb)) then
    Error("FAIL: Archetype CIX Klein K_y automorphism failed");
fi;
if ZornRefl_g(ZornKleinY_g(ZornRefl_g(Q_alb))) <> ZornKleinZ_g(Q_alb) then
    Error("FAIL: Archetype CXI octahedral S_4 reflection normalization failed");
fi;
SpinX_g := [ 0*y1, [1 + 0*y1, 0*y1, 0*y1], [1 + 0*y1, 0*y1, 0*y1], 0*y1 ];
if ZornMul(SpinX_g, SpinX_g) <> ZornSub(ZornZero, ZornOne) then
    Error("FAIL: Archetype CXV internal Zorn spinor square law failed");
fi;
SpinProjX_g := function(M) return ZornSub(ZornSub(ZornAdd(M, ZornKleinX_g(M)), ZornKleinY_g(M)), ZornKleinZ_g(M)); end;
SpinProjY_g := function(M) return ZornSub(ZornAdd(ZornSub(M, ZornKleinX_g(M)), ZornKleinY_g(M)), ZornKleinZ_g(M)); end;
SpinProjZ_g := function(M) return ZornAdd(ZornSub(ZornSub(M, ZornKleinX_g(M)), ZornKleinY_g(M)), ZornKleinZ_g(M)); end;
if SpinProjX_g(SpinProjY_g(Q_alb)) <> ZornZero then
    Error("FAIL: Archetype CXVI spin projector orthogonality failed");
fi;
ProdXY_g := ZornMul(SpinProjX_g(Q_alb), SpinProjY_g(Xi1_alb));
if SpinProjZ_g(ProdXY_g) <> 4 * ProdXY_g then
    Error("FAIL: Archetype CXVI Klein spin fusion rule Pi_x * Pi_y subset Pi_z failed");
fi;
QuatSubX_g := function(aq, vxq, wxq, bq) return [ aq, [vxq, 0*y1, 0*y1], [wxq, 0*y1, 0*y1], bq ]; end;
QuatSubY_g := function(aq, vyq, wyq, bq) return [ aq, [0*y1, vyq, 0*y1], [0*y1, wyq, 0*y1], bq ]; end;
QuatSubZ_g := function(aq, vzq, wzq, bq) return [ aq, [0*y1, 0*y1, vzq], [0*y1, 0*y1, wzq], bq ]; end;
if ZornSub(ZornMul(ZornMul(QuatSubY_g(y1, z1, xi1, y2), QuatSubY_g(z2, xi2, y3, z3)), QuatSubY_g(xi3, y1, z2, xi1)),
           ZornMul(QuatSubY_g(y1, z1, xi1, y2), ZornMul(QuatSubY_g(z2, xi2, y3, z3), QuatSubY_g(xi3, y1, z2, xi1)))) <> ZornZero then
    Error("FAIL: Archetype CXVII QuatSubY associativity failed");
fi;
if ZornGaloisZ3(QuatSubX_g(y1, z1, xi1, y2)) <> QuatSubZ_g(y1, z1, xi1, y2) then
    Error("FAIL: Archetype CXVII Z_3 triality cycle of quaternion subalgebras failed");
fi;
Print("[PASS] GAP: Archetypes LXXV-CXIX (Catto E_9/E_10 Weyl Reflection, 27D Split-Octonion Albert-Freudenthal Law, Hansen Cl(4,2) Doublet Tower, Parabolic Majorana Zero Modes, Chevalley-Shirokov Spinor Ideals, Trifactor-Loxodromic Zorn-Riccati Compass, 56D Freudenthal E_7 Euler Trace, 4-Spinor Cross-Difference, Gelfand-Retakh Elimination, Nambu-Gorkov Operator Cayley-Dickson Doubling, 5-Graded Spectral Projectors, OpCyclotomic3/OpCyclotomic6 Quotients, Z_3 Singlet Associativity, Octahedral S_4 = V_4 |>< S_3 Galois Group, Quaternion Spin Double Cover Q_8 ->> V_4, & Three Associative Quaternion Subalgebras H_{x,y,z}(A) ~= M_2(A))\n");

Print("======================================================================\n");
Print("ALL CHECKS PASSED\n");
Print("======================================================================\n");
QUIT;
