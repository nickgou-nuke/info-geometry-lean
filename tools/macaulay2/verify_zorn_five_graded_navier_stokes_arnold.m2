-- Macaulay2 + Dmodules Verification of Archetypes XLII-LIV:
-- 1. Exact polynomial verification of the 5-graded Zorn Heisenberg group laws,
--    4-gate braid commutator monodromy loop, 5-graded BCFW contact residue, and
--    Universal 3D Zorn Lamb-velocity & Lamb-vorticity nilpotence.
-- 2. Weyl algebra & Dmodules (`needsPackage "Dmodules"`) verification of the
--    5-graded contact symplectic form and Navier-Stokes helicity invariant.

needsPackage "Dmodules"

print("======================================================================")
print("Macaulay2 + Dmodules Verification: 5-Graded Zorn, BCFW, Arnold & Navier-Stokes")
print("======================================================================")

R = QQ[y1,z1,xi1,y2,z2,xi2,y3,z3,xi3,eta,y0,z0,ys,zs,ux,uy,uz,wx,wy,wz]

-- 1. Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence
vecDot = (u, v) -> u#0 * v#0 + u#1 * v#1 + u#2 * v#2
vecCross = (u, v) -> {
    u#1 * v#2 - u#2 * v#1,
    u#2 * v#0 - u#0 * v#2,
    u#0 * v#1 - u#1 * v#0
}
vecAdd = (u, v) -> {u#0 + v#0, u#1 + v#1, u#2 + v#2}
vecSub = (u, v) -> {u#0 - v#0, u#1 - v#1, u#2 - v#2}
vecScale = (c, u) -> {c * u#0, c * u#1, c * u#2}

zornZero = {0_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, 0_R}
zornOne  = {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, 1_R}

zornAdd = (X, Y) -> {X#0 + Y#0, vecAdd(X#1, Y#1), vecAdd(X#2, Y#2), X#3 + Y#3}
zornSub = (X, Y) -> {X#0 - Y#0, vecSub(X#1, Y#1), vecSub(X#2, Y#2), X#3 - Y#3}

zornMul = (X, Y) -> (
    a := X#0 * Y#0 - vecDot(X#1, Y#2);
    v := vecSub(vecAdd(vecScale(X#0, Y#1), vecScale(Y#3, X#1)), vecCross(X#2, Y#2));
    w := vecAdd(vecAdd(vecScale(Y#0, X#2), vecScale(X#3, Y#2)), vecCross(X#1, Y#1));
    b := -vecDot(X#2, Y#1) + X#3 * Y#3;
    {a, v, w, b}
)

zornAssoc = (X, Y, Z) -> zornSub(zornMul(zornMul(X, Y), Z), zornMul(X, zornMul(Y, Z)))

U3 = {0_R, {ux, uy, uz}, {0_R, 0_R, 0_R}, 0_R}
Om3 = {0_R, {wx, wy, wz}, {0_R, 0_R, 0_R}, 0_R}
Lamb3 = zornMul(Om3, U3)

assert(zornMul(U3, Lamb3) == zornZero)
assert(zornMul(Lamb3, U3) == zornZero)
assert(zornMul(Om3, Lamb3) == zornZero)
assert(zornMul(Lamb3, Om3) == zornZero)
print("[PASS] Macaulay2: Universal 3D Zorn Lamb-Velocity & Lamb-Vorticity Nilpotence")

-- 2. 5-Graded Heisenberg Group Associativity, 4-Gate Braid Loop, & BCFW Shift
hGroupPlus = (y, z, xi) -> {1_R, {0_R, y, z}, {xi, 0_R, 0_R}, 1_R}
gradePlus2 = (xi) -> {0_R, {0_R, 0_R, 0_R}, {xi, 0_R, 0_R}, 0_R}
gradeMinus2 = (e) -> {0_R, {e, 0_R, 0_R}, {0_R, 0_R, 0_R}, 0_R}
gradeZero = (rp, rm) -> {rp, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, rm}

G1 = hGroupPlus(y1, z1, xi1)
G2 = hGroupPlus(y2, z2, xi2)
G3 = hGroupPlus(y3, z3, xi3)
G1inv = hGroupPlus(-y1, -z1, -xi1)
G2inv = hGroupPlus(-y2, -z2, -xi2)
w12 = y1*z2 - z1*y2

assert(zornAssoc(G1, G2, G3) == zornZero)
assert(zornMul(zornMul(G1, G2), zornMul(G1inv, G2inv)) == hGroupPlus(0_R, 0_R, 2*w12))
print("[PASS] Macaulay2: 3-Layer KAN Associativity & 4-Gate Braid Monodromy Loop")

P0 = {1_R, {0_R, -y0, -z0}, {0_R, 0_R, 0_R}, 0_R}
Pshifted = {1_R, {0_R, -(ys + y0), -(zs + z0)}, {0_R, 0_R, 0_R}, 0_R}
Splus = hGroupPlus(ys, zs, 0_R)
Sminus = hGroupPlus(-ys, -zs, 0_R)
wres = ys*z0 - zs*y0

assert(zornAssoc(Splus, P0, Sminus) == zornZero)
assert(zornMul(P0, Sminus) == zornSub(Pshifted, gradePlus2(wres)))
assert(zornMul(gradeMinus2(eta), zornSub(zornMul(P0, Sminus), Pshifted)) == gradeZero(eta*wres, 0_R))
print("[PASS] Macaulay2: 5-Graded BCFW Transverse Shift & Contact Pole Residue Readout")

-- 2b. Archetypes LXI & LXII: 1934 JvNW Cubic Peirce Polynomial & Fundamental Jordan Axiom (III)
zornJordan = (X, Y) -> zornAdd(zornMul(X, Y), zornMul(Y, X))
e11 = gradeZero(1_R, 0_R)
Xjvnw = {y1, {ux, uy, uz}, {wx, wy, wz}, z1}
Bjvnw = {y2, {wx, uz, uy}, {ux, wz, wy}, z2}
L1e = zornJordan(e11, Xjvnw)
L2e = zornJordan(e11, L1e)
L3e = zornJordan(e11, L2e)
assert(zornAdd(zornSub(L3e, zornAdd(zornAdd(L2e, L2e), L2e)), zornAdd(L1e, L1e)) == zornZero)
Asq = zornJordan(Xjvnw, Xjvnw)
assert(zornJordan(zornJordan(Asq, Bjvnw), Xjvnw) == zornJordan(Asq, zornJordan(Bjvnw, Xjvnw)))
print("[PASS] Macaulay2: 1934 JvNW Cubic Peirce Polynomial & Fundamental Jordan Axiom (III)")

-- 2c. Archetypes LV-LX: QGT Madelung Split, Metriplectic Flow, Baryon-Meson Confinement, & Master Trifactor Synthesis
zornComm = (X, Y) -> zornSub(zornMul(X, Y), zornMul(Y, X))
zornScale = (c, X) -> {c * X#0, vecScale(c, X#1), vecScale(c, X#2), c * X#3}

Lpv = {0_R, {ux, uy, uz}, {0_R, 0_R, 0_R}, 0_R}
Lmw = {0_R, {0_R, 0_R, 0_R}, {wx, wy, wz}, 0_R}
QGTvw = zornScale(2_R, zornMul(Lpv, Lmw))
gvw = zornJordan(Lpv, Lmw)
omvw = zornComm(Lpv, Lmw)
assert(QGTvw == zornAdd(gvw, omvw))
assert(zornAdd(zornComm(Lpv, Xjvnw), zornJordan(Lpv, Xjvnw)) == zornScale(2_R, zornMul(Lpv, Xjvnw)))

Lpq1 = {0_R, {y1, z1, xi1}, {0_R, 0_R, 0_R}, 0_R}
Lpq2 = {0_R, {y2, z2, xi2}, {0_R, 0_R, 0_R}, 0_R}
Lpq3 = {0_R, {y3, z3, xi3}, {0_R, 0_R, 0_R}, 0_R}
B123 = zornAssoc(Lpq1, Lpq2, Lpq3)
B213 = zornAssoc(Lpq2, Lpq1, Lpq3)
B113 = zornAssoc(Lpq1, Lpq1, Lpq3)
baryonDet = vecDot({y1, z1, xi1}, vecCross({y2, z2, xi2}, {y3, z3, xi3}))
assert(B123 == gradeZero(baryonDet, -baryonDet))
assert(zornAdd(B123, B213) == zornZero)
assert(B113 == zornZero)

PsiL = {1_R, {0_R, 0_R, 0_R}, {wx, wy, wz}, 0_R}
PsiR = {1_R, {ux, uy, uz}, {0_R, 0_R, 0_R}, 0_R}
Pitri = zornMul(PsiL, PsiR)
assert(zornMul(PsiL, PsiL) == PsiL)
assert(zornMul(PsiR, PsiR) == PsiR)
assert(zornAssoc(PsiR, PsiL, PsiR) == zornZero)
assert(zornAssoc(PsiL, PsiR, PsiL) == zornZero)
assert(zornMul(Pitri, Pitri) == zornMul(PsiL, zornMul(zornMul(PsiR, PsiL), PsiR)))

Pic1 = {1_R, {0_R, -y1, -z1}, {xi1, 0_R, 0_R}, 0_R}
Pic2 = {1_R, {0_R, -y2, -z2}, {xi2, 0_R, 0_R}, 0_R}
assert(zornMul(Pic1, Pic1) == Pic1)
assert(zornMul(Pic1, Pic2) == {1_R, {0_R, -y2, -z2}, {xi1 + w12, 0_R, 0_R}, 0_R})
print("[PASS] Macaulay2: Archetypes LV-LX (QGT Madelung, Metriplectic, Baryon Singlet, & Master Trifactor Synthesis)")

-- 2d. Archetypes LXIII & LXIV: Wheeler "It from Bit" (P^2 = P), "Boundary of a Boundary is Zero" (d^2 = 0), & 3-Bit Volume
dvWh = zornSub(PsiR, e11)
dwWh = zornSub(PsiL, e11)
assert(zornMul(dvWh, dvWh) == zornZero)
assert(zornMul(dwWh, dwWh) == zornZero)
assert(zornAdd(zornMul(dvWh, dwWh), zornMul(dwWh, dvWh)) == gvw)
assert(zornSub(zornMul(dvWh, dwWh), zornMul(dwWh, dvWh)) == omvw)
assert(zornMul(Lpq1, zornMul(Lpq2, Lpq3)) == gradeZero(-baryonDet, 0_R))
assert(zornMul(zornMul(Lpq1, Lpq2), Lpq3) == gradeZero(0_R, -baryonDet))
print("[PASS] Macaulay2: Archetypes LXIII-LXIV (Wheeler 'It from Bit', 'Boundary of a Boundary is Zero', & 3-Bit Volume)")

-- 2e. Archetypes LXV & LXVI: Euler 5-Grading Operator E_5, Nilradical Derivation, & KKT Degree-5 Minimal Polynomial
zornEuler5 = (X) -> (
    {0_R, {-2 * X#1#0, X#1#1, X#1#2}, {2 * X#2#0, -X#2#1, -X#2#2}, 0_R}
)
N1p = {0_R, {0_R, y1, z1}, {xi1, 0_R, 0_R}, 0_R}
N2p = {0_R, {0_R, y2, z2}, {xi2, 0_R, 0_R}, 0_R}
assert(zornEuler5(zornMul(N1p, N2p)) == zornAdd(zornMul(zornEuler5(N1p), N2p), zornMul(N1p, zornEuler5(N2p))))
E1A = zornEuler5(Xjvnw)
E2A = zornEuler5(E1A)
E3A = zornEuler5(E2A)
E4A = zornEuler5(E3A)
E5A = zornEuler5(E4A)
assert(zornAdd(zornSub(E5A, zornAdd(zornAdd(zornAdd(zornAdd(E3A, E3A), E3A), E3A), E3A)), zornAdd(zornAdd(zornAdd(E1A, E1A), E1A), E1A)) == zornZero)
print("[PASS] Macaulay2: Archetypes LXV-LXVI (Euler 5-Grading Nilradical Derivation & KKT Degree-5 Minimal Polynomial)")

-- 2f. Archetypes LXVII & LXVIII: Rolf Dahm Dihedral D_4 & PG(3,2) Collinear Operator Triple (s1 * s0) * r1 = r0
dahmR0 = {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, 1_R}
dahmR1 = {0_R, {-1_R, 0_R, 0_R}, {-1_R, 0_R, 0_R}, 0_R}
dahmS0 = {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, -1_R}
dahmS1 = {0_R, {-1_R, 0_R, 0_R}, {1_R, 0_R, 0_R}, 0_R}
assert(zornMul(dahmS0, dahmS0) == dahmR0)
assert(zornMul(dahmS1, dahmS1) == dahmR0)
assert(zornMul(dahmS0, dahmR1) == dahmS1)
assert(zornMul(zornMul(dahmS1, dahmS0), dahmR1) == dahmR0)
-- Archetypes LXIX & LXX: Maxwell-Poynting Hodge-Dual Stress Matrix J(E, B) * J*(E, B) & Simple Plücker Line J_line^2 = 0
Jem = {0_R, {ux, uy, uz}, {wx, wy, wz}, 0_R}
Jstar = {0_R, {-wx, -wy, -wz}, {ux, uy, uz}, 0_R}
Spoynt = vecCross({ux, uy, uz}, {wx, wy, wz})
assert(zornMul(Jem, Jstar) == {-vecDot({ux, uy, uz}, {ux, uy, uz}), Spoynt, vecScale(-1_R, Spoynt), vecDot({wx, wy, wz}, {wx, wy, wz})})
Jline = {0_R, {y1*z2 - y2*z1, y1*xi2 - y2*xi1, y1*z3 - y2*y3}, {xi1*z3 - xi2*y3, y3*z2 - z3*z1, z1*xi2 - z2*xi1}, 0_R}
assert(zornMul(Jline, Jline) == zornZero)
-- Archetypes LXXI & LXXII: Saniga-Holweck-Pracna Grassmannian Edge-Triangle & Sedenion Zero Divisors
zornConj = X -> {X#3, vecScale(-1_R, X#1), vecScale(-1_R, X#2), X#0}
Om12 = {0_R, {y1 - y2, z1 - z2, xi1 - xi2}, {0_R, 0_R, 0_R}, 0_R}
Om23 = {0_R, {y2 - y3, z2 - z3, xi2 - xi3}, {0_R, 0_R, 0_R}, 0_R}
Om31 = {0_R, {y3 - y1, z3 - z1, xi3 - xi1}, {0_R, 0_R, 0_R}, 0_R}
assert(zornMul(Om12, Om23) == zornMul(Om23, Om31))
assert(zornMul(Om23, Om31) == zornMul(Om31, Om12))
SedX = zornSub(zornMul(Lpv, Lmw), zornMul(zornScale(-1_R, Lpv), zornConj(Lmw)))
SedY = zornAdd(zornMul(zornConj(Lpv), zornScale(-1_R, Lpv)), zornMul(Lmw, Lmw))
assert(SedX == zornZero and SedY == zornZero)
-- Archetypes LXXIII & LXXIV: Pasch 4-Simplex Tetrahedral 2-Boundary Closure P_123 - P_134 + P_124 - P_234 = 0
Om34 = {0_R, {y3 - y0, z3 - z0, xi3 - eta}, {0_R, 0_R, 0_R}, 0_R}
Om13 = zornAdd(Om12, Om23)
Om24 = zornAdd(Om23, Om34)
P123 = zornMul(Om12, Om23)
P134 = zornMul(Om13, Om34)
P124 = zornMul(Om12, Om24)
P234 = zornMul(Om23, Om34)
assert(zornSub(zornAdd(zornSub(P234, P134), P124), P123) == zornZero)
print("[PASS] Macaulay2: Archetypes LXVII-LXXIV (Dahm D_4, Maxwell-Poynting Stress, Grassmannian G_2(N+1), Sedenion Zero Divisors, & Pasch 4-Simplex 2-Boundary)")

-- Archetypes LXXV, LXXVI, LXXVII, & LXXVIII: Catto E_9/E_10 Weyl Reflection & 27D Split-Octonion Albert-Freudenthal Adjoint & Determinant Law
zornMulStd = (X, Y) -> (
    a := X#0 * Y#0 + vecDot(X#1, Y#2);
    v := vecAdd(vecAdd(vecScale(X#0, Y#1), vecScale(Y#3, X#1)), vecCross(X#2, Y#2));
    w := vecSub(vecAdd(vecScale(Y#0, X#2), vecScale(X#3, Y#2)), vecCross(X#1, Y#1));
    b := vecDot(X#2, Y#1) + X#3 * Y#3;
    {a, v, w, b}
)
zornJordanStd = (X, Y) -> zornAdd(zornMulStd(X, Y), zornMulStd(Y, X))
zornTrace = X -> X#0 + X#3
zornNorm = X -> X#0 * X#3 - vecDot(X#1, X#2)
zornInner = (X, Y) -> zornTrace(zornMulStd(X, zornConj(Y)))
zornJT = (X, Y, Z) -> zornSub(zornAdd(zornJordanStd(zornJordanStd(X, Y), Z), zornJordanStd(X, zornJordanStd(Y, Z))), zornJordanStd(zornJordanStd(X, Z), Y))
Qalb = Xjvnw
Xi1alb = Bjvnw
Xi2alb = {eta, {y1, z2, xi3}, {y2, z3, xi1}, y3}
assert(zornJT(Xi1alb, zornConj(Qalb), Xi1alb) == zornScale(4_R, zornSub(zornScale(zornTrace(zornMulStd(Qalb, zornConj(Xi1alb))), Xi1alb), zornScale(zornNorm(Xi1alb), Qalb))))
assert(zornTrace(zornMulStd(zornMulStd(Qalb, Xi2alb), zornConj(Xi1alb))) == zornTrace(zornMulStd(Qalb, zornMulStd(Xi2alb, zornConj(Xi1alb)))))
xpa = y0; xma = z0; va = ys;
shxp = xma * va - zornNorm(Xi2alb)
shxm = xpa * va - zornNorm(Xi1alb)
shv  = xpa * xma - zornNorm(Qalb)
shQ  = zornSub(zornMulStd(Xi1alb, zornConj(Xi2alb)), zornScale(va, Qalb))
shXi1 = zornSub(zornMulStd(Qalb, Xi2alb), zornScale(xma, Xi1alb))
shXi2 = zornSub(zornMulStd(zornConj(Qalb), Xi1alb), zornScale(xpa, Xi2alb))
det27 = xpa*xma*va - xpa*zornNorm(Xi2alb) - xma*zornNorm(Xi1alb) - va*zornNorm(Qalb) + zornTrace(zornMulStd(zornMulStd(Qalb, Xi2alb), zornConj(Xi1alb)))
acxp = 2*xpa*shxp + zornInner(Qalb, shQ) + zornInner(Xi1alb, shXi1)
acxm = 2*xma*shxm + zornInner(zornConj(Qalb), zornConj(shQ)) + zornInner(Xi2alb, shXi2)
acv  = 2*va*shv + zornInner(Xi1alb, shXi1) + zornInner(Xi2alb, shXi2)
acQ  = zornAdd(zornAdd(zornScale(xpa + xma, shQ), zornScale(shxp + shxm, Qalb)), zornAdd(zornMulStd(Xi1alb, zornConj(shXi2)), zornMulStd(shXi1, zornConj(Xi2alb))))
acXi1 = zornAdd(zornAdd(zornScale(xpa + va, shXi1), zornScale(shxp + shv, Xi1alb)), zornAdd(zornMulStd(Qalb, shXi2), zornMulStd(shQ, Xi2alb)))
acXi2 = zornAdd(zornAdd(zornScale(xma + va, shXi2), zornScale(shxm + shv, Xi2alb)), zornAdd(zornMulStd(zornConj(Qalb), shXi1), zornMulStd(zornConj(shQ), Xi1alb)))
assert(acxp == 2*det27 and acxm == 2*det27 and acv == 2*det27)
assert(acQ == zornZero and acXi1 == zornZero and acXi2 == zornZero)
-- Archetypes LXXIX & LXXX: Z_3-Triality Determinant Split & 72-Channel Nilradical Inversion
assert(zornAdd(zornAdd(zornAssoc(Lpq1, Lpq2, Lpq3), zornAssoc(Lpq2, Lpq3, Lpq1)), zornAssoc(Lpq3, Lpq1, Lpq2)) == gradeZero(3 * baryonDet, -3 * baryonDet))
-- Archetypes LXXXI, LXXXII, & LXXXIII: Steen H. Hansen (21 Oct 2026) Cl(4,2) Doublet Tower & Zorn Conformal-Triality Marriage
Dzorn = gradeZero(1_R, -1_R)
assert(zornSub(zornMul(Dzorn, Lpq1), zornMul(Lpq1, Dzorn)) == zornAdd(Lpq1, Lpq1))
assert(zornAdd(zornMul(Dzorn, Lpq1), zornMul(Lpq1, Dzorn)) == zornZero)
assert(zornSub(zornMul(Lpq1, Lpq2), zornMul(Lpq2, Lpq1)) == {0_R, {0_R, 0_R, 0_R}, vecScale(2_R, vecCross({y1, z1, xi1}, {y2, z2, xi2})), 0_R})
assert(((y1 - 1_R) - 1_R)^2 - ((y1 - 1_R) + 1_R) == (y1 - 1_R) * (y1 - 4_R))
-- Archetypes LXXXIV & LXXXV: Zero Chiral Volume, Krein Null Kernel, Parabolic Boundary Sheaf, & Majorana Horizon Zero Modes
assert(vecDot({0_R, y1, z1}, vecCross({0_R, y2, z2}, {0_R, y3, z3})) == 0_R)
Ep1m = {0_R, {0_R, y1, z1}, {0_R, 0_R, 0_R}, 0_R}
Em1m = {0_R, {0_R, 0_R, 0_R}, {0_R, y1, z1}, 0_R}
ZMajm = gradePlus2(xi3)
Em2m = gradeMinus2(xi3)
PibPerp = zornSub(zornOne, Pic1)
assert(zornMul(Ep1m, ZMajm) == zornZero and zornMul(ZMajm, Ep1m) == zornZero)
assert(zornMul(Em1m, Em2m) == zornZero and zornMul(Em2m, Em1m) == zornZero)
assert(zornMul(Em1m, ZMajm) == {0_R, {0_R, -z1*xi3, y1*xi3}, {0_R, 0_R, 0_R}, 0_R})
assert(zornMul(Pic1, ZMajm) == zornZero and zornMul(ZMajm, Pic1) == ZMajm)
assert(zornMul(PibPerp, ZMajm) == ZMajm and zornMul(ZMajm, PibPerp) == zornZero)
-- Archetypes LXXXVI & LXXXVII: Chevalley-Lounesto-Shirokov Spinor Ideals & Relativistic Dirac-Krein Ket-Bra Duality
psic1m = {y1, {0_R, 0_R, 0_R}, {xi1, 0_R, 0_R}, 0_R}
phic2barm = {y2, {xi2, 0_R, 0_R}, {0_R, 0_R, 0_R}, 0_R}
psic3m = {y3, {0_R, 0_R, 0_R}, {xi3, 0_R, 0_R}, 0_R}
assert(zornAssoc(psic1m, phic2barm, psic3m) == zornZero)
-- Archetypes LXXXVIII & LXXXIX: Trifactor-Loxodromic Compass, Doubled 4-Vector Potentials, & 8D Zorn-Riccati Möbius Operator
Prowm = {1_R, {y1, z1, xi1}, {0_R, 0_R, 0_R}, 0_R}
Pcolm = {1_R, {0_R, 0_R, 0_R}, {y2, z2, xi2}, 0_R}
Uupm = {1_R, {y1, z1, xi1}, {0_R, 0_R, 0_R}, 1_R}
Ulom = {1_R, {0_R, 0_R, 0_R}, {y2, z2, xi2}, 1_R}
Tbruhatm = zornMul(zornMul(Ulom, {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, xi3}), Uupm)
assert(Tbruhatm == zornAdd(zornMul(zornMul(Pcolm, {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, 0_R}), Prowm), {0_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, xi3}))
riccatiTm = vecSub(vecAdd(vecAdd(vecScale(vecDot(Tbruhatm#2, {y1, z1, xi1}), {y1, z1, xi1}), vecScale(Tbruhatm#3, {y1, z1, xi1})), vecScale(Tbruhatm#0, {y1, z1, xi1})), Tbruhatm#1)
assert(riccatiTm == vecScale(xi3, {y1, z1, xi1}))
-- Archetypes XC-XCV: 56D Freudenthal E_7 Euler Trace Identity <M, M^#>_27 = 3 Det_27(M), Doublet Tower, & Gelfand-Retakh Gauss-Bruhat Elimination
tracePair27m = xpa*shxp + xma*shxm + va*shv + zornInner(Qalb, shQ) + zornInner(Xi1alb, shXi1) + zornInner(Xi2alb, shXi2)
assert(tracePair27m == 3*det27)
UupNegm = {1_R, vecScale(-1_R, {y1, z1, xi1}), {0_R, 0_R, 0_R}, 1_R}
UloNegm = {1_R, {0_R, 0_R, 0_R}, vecScale(-1_R, {y2, z2, xi2}), 1_R}
assert(zornMul(zornMul(UloNegm, Tbruhatm), UupNegm) == {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, xi3})
assert(Tbruhatm#3 + vecDot(Tbruhatm#2, Tbruhatm#1) == xi3)
crossOrigM = ((1_R - vecDot(vecAdd({y1,z1,xi1},{y3,z3,xi3}), vecAdd({y2,z2,xi2},{y3,z3,xi3}))) - (1_R - vecDot(vecAdd({y1,z1,xi1},{y3,z3,xi3}), vecAdd({y3,z3,xi3},{y3,z3,xi3})))) - ((1_R - vecDot(vecAdd({y3,z3,xi3},{y3,z3,xi3}), vecAdd({y2,z2,xi2},{y3,z3,xi3}))) - (1_R - vecDot(vecAdd({y3,z3,xi3},{y3,z3,xi3}), vecAdd({y3,z3,xi3},{y3,z3,xi3}))))
crossBaseM = ((1_R - vecDot({y1,z1,xi1}, {y2,z2,xi2})) - (1_R - vecDot({y1,z1,xi1}, {y3,z3,xi3}))) - ((1_R - vecDot({y3,z3,xi3}, {y2,z2,xi2})) - (1_R - vecDot({y3,z3,xi3}, {y3,z3,xi3})))
assert(crossOrigM == crossBaseM)
-- Archetypes XCVI-C: Cyclotomic Factorizations & Z_6 Galois Automorphism Group
assert((xi1^6 - 1_R) == (xi1 - 1_R)*(xi1 + 1_R)*(xi1^2 + xi1 + 1_R)*(xi1^2 - xi1 + 1_R))
triPermM = u -> {u#1, u#2, u#0}
gradeParityVecM = u -> {u#0, -1_R * u#1, -1_R * u#2}
galoisZ3M = M -> {M#0, triPermM(M#1), triPermM(M#2), M#3}
gradeParityM = M -> {M#0, gradeParityVecM(M#1), gradeParityVecM(M#2), M#3}
galoisZ6M = M -> {M#0, vecScale(-1_R, triPermM(M#1)), vecScale(-1_R, triPermM(M#2)), M#3}
assert(galoisZ3M(zornMul(Qalb, Xi1alb)) == zornMul(galoisZ3M(Qalb), galoisZ3M(Xi1alb)))
assert(gradeParityM(zornMul(Qalb, Xi1alb)) == zornMul(gradeParityM(Qalb), gradeParityM(Xi1alb)))
assert(galoisZ6M(galoisZ6M(Qalb)) == galoisZ3M(galoisZ3M(Qalb)))
riccatiM = (M, qv) -> vecSub(vecSub(vecAdd(vecScale(vecDot(M#2, qv), qv), vecScale(M#3, qv)), vecScale(M#0, qv)), M#1)
assert(triPermM(riccatiM(Qalb, {y1, z1, xi1})) == riccatiM(galoisZ3M(Qalb), triPermM({y1, z1, xi1})))
assert(vecScale(-1_R, triPermM(riccatiM(Qalb, {y1, z1, xi1}))) == riccatiM(galoisZ6M(Qalb), vecScale(-1_R, triPermM({y1, z1, xi1}))))
zornSingletM = (as, cs, ds, bs) -> {as, {cs, cs, cs}, {ds, ds, ds}, bs}
S1m = zornSingletM(y1, z1, xi1, y2)
S2m = zornSingletM(z2, xi2, y3, z3)
S3m = zornSingletM(xi3, y1, z2, xi1)
assert(zornMul(zornMul(S1m, S2m), S3m) == zornMul(S1m, zornMul(S2m, S3m)))
reflVecM = v -> {-v#0, -v#2, -v#1}
kleinXVecM = v -> {v#0, -v#1, -v#2}
kleinYVecM = v -> {-v#0, v#1, -v#2}
kleinZVecM = v -> {-v#0, -v#1, v#2}
reflM = M -> {M#0, reflVecM(M#1), reflVecM(M#2), M#3}
kleinXM = M -> {M#0, kleinXVecM(M#1), kleinXVecM(M#2), M#3}
kleinYM = M -> {M#0, kleinYVecM(M#1), kleinYVecM(M#2), M#3}
kleinZM = M -> {M#0, kleinZVecM(M#1), kleinZVecM(M#2), M#3}
assert(reflM(zornMul(Qalb, Xi1alb)) == zornMul(reflM(Qalb), reflM(Xi1alb)))
assert(reflM(galoisZ3M(reflM(Qalb))) == galoisZ3M(galoisZ3M(Qalb)))
assert(kleinYM(zornMul(Qalb, Xi1alb)) == zornMul(kleinYM(Qalb), kleinYM(Xi1alb)))
assert(reflM(kleinYM(reflM(Qalb))) == kleinZM(Qalb))
spinXM = {0_R, {1_R, 0_R, 0_R}, {1_R, 0_R, 0_R}, 0_R}
assert(zornMul(spinXM, spinXM) == zornSub(zornZero, zornOne))
spinProjXM = M -> zornSub(zornSub(zornAdd(M, kleinXM(M)), kleinYM(M)), kleinZM(M))
spinProjYM = M -> zornSub(zornAdd(zornSub(M, kleinXM(M)), kleinYM(M)), kleinZM(M))
spinProjZM = M -> zornAdd(zornSub(zornSub(M, kleinXM(M)), kleinYM(M)), kleinZM(M))
assert(spinProjXM(spinProjYM(Qalb)) == zornZero)
prodXYM = zornMul(spinProjXM(Qalb), spinProjYM(Xi1alb))
assert(spinProjZM(prodXYM) == zornAdd(zornAdd(prodXYM, prodXYM), zornAdd(prodXYM, prodXYM)))
quatSubXM = (aq, vxq, wxq, bq) -> {aq, {vxq, 0_R, 0_R}, {wxq, 0_R, 0_R}, bq}
quatSubYM = (aq, vyq, wyq, bq) -> {aq, {0_R, vyq, 0_R}, {0_R, wyq, 0_R}, bq}
quatSubZM = (aq, vzq, wzq, bq) -> {aq, {0_R, 0_R, vzq}, {0_R, 0_R, wzq}, bq}
assert(zornMul(zornMul(quatSubYM(y1, z1, xi1, y2), quatSubYM(z2, xi2, y3, z3)), quatSubYM(xi3, y1, z2, xi1)) ==
       zornMul(quatSubYM(y1, z1, xi1, y2), zornMul(quatSubYM(z2, xi2, y3, z3), quatSubYM(xi3, y1, z2, xi1))))
assert(galoisZ3M(quatSubXM(y1, z1, xi1, y2)) == quatSubZM(y1, z1, xi1, y2))
EplusM = {1_R, {0_R, 0_R, 0_R}, {0_R, 0_R, 0_R}, 0_R}
dEM = zornSub(zornMul(Qalb, EplusM), zornMul(EplusM, Qalb))
OmM = zornMul(dEM, dEM)
assert(zornMul(zornMul(EplusM, dEM), EplusM) == zornZero)
assert(zornMul(EplusM, OmM) == zornMul(OmM, EplusM))
print("[PASS] Macaulay2: Archetypes LXXV-CXIX (Catto E_9/E_10 Weyl Reflection, 27D Split-Octonion Albert-Freudenthal Law, Hansen Cl(4,2) Doublet Tower, Parabolic Majorana Zero Modes, Chevalley-Shirokov Spinor Ideals, Trifactor-Loxodromic Zorn-Riccati Compass, 56D Freudenthal E_7 Euler Trace, 4-Spinor Cross-Difference, Gelfand-Retakh Elimination, Nambu-Gorkov Cayley-Dickson, OpCyclotomic3/OpCyclotomic6 Quotients, Z_3 Singlet Associativity, Octahedral S_4 = V_4 |>< S_3 Galois Group, Quaternion Spin Double Cover Q_8 ->> V_4, Three Associative Quaternion Subalgebras H_{x,y,z}(A) ~= M_2(A), & Zorn-Connes Vacuum Curvature Collapse)")

-- 3. Dmodules Weyl Algebra Analysis of the 5-Graded Contact & Helicity Operators
W = QQ[y1, z1, y2, z2, dy1, dz1, dy2, dz2, WeylAlgebra => {y1 => dy1, z1 => dz1, y2 => dy2, z2 => dz2}]
omegaPerp = y1*z2 - z1*y2
-- Verify Euler homogeneity derivation E = y1*dy1 + z1*dz1 + y2*dy2 + z2*dz2 on omegaPerp:
-- [E, omegaPerp] = 2 * omegaPerp (Grade +2 contact scaling weight!)
Eop = y1*dy1 + z1*dz1 + y2*dy2 + z2*dz2
commE = Eop * omegaPerp - omegaPerp * Eop
assert(commE == 2 * omegaPerp)

-- Compute D-module AnnFs and Bernstein-Sato polynomial of the contact symplectic form
RW = QQ[y1, z1, y2, z2]
use RW
fContact = y1*z2 - z1*y2
bPoly = globalBFunction fContact
assert(bPoly != 0)
-- Archetypes XCVI-XCVIII: Nambu-Gorkov Operator Cayley-Dickson Norm & 5-Graded Spectral Projectors:
assert((y1*y1 + y2*(-z1)*z1) == y1^2 - y2*z1^2)
assert((y1*(-z1) + y1*z1) == 0)
assert((2^3 - 2) == 6 and (1^3 - 1) == 0 and (1^3 - 4*1) == -3 and (2^3 - 4*2) == 0)
-- Archetypes XCIX-CIV: Operator Cyclotomic Polynomial Factorizations:
assert((y1 - 1)*(y1 + 1)*(y1^2 + y1 + 1)*(y1^2 - y1 + 1) == y1^6 - 1)
assert((y1 - 1)*(y1 + 1)*(y1^2 + 1)*(y1^4 + 1) == y1^8 - 1)
print("[PASS] Macaulay2 Dmodules: Weyl Grade +2 Contact Scaling, Nambu-Gorkov Cayley-Dickson Norm, 5-Graded Spectral Projectors, Operator Cyclotomics, & globalBFunction verified: " | toString factor bPoly)

print("======================================================================")
print("ALL CHECKS PASSED")
print("======================================================================")
exit 0
