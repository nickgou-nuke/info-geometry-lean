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

Print("======================================================================\n");
Print("ALL CHECKS PASSED\n");
Print("======================================================================\n");
QUIT;
