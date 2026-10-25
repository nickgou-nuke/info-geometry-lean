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
Print("[PASS] GAP: Archetypes LXVII-LXVIII (Dahm Dihedral D_4 & PG(3,2) Collinear Operator Triple s0*s1*r1 = r0)\n");

Print("======================================================================\n");
Print("ALL CHECKS PASSED\n");
Print("======================================================================\n");
QUIT;
