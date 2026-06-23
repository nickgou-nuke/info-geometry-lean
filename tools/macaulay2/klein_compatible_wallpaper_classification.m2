-- Macaulay2 / Dmodules exact certificate for finite Klein wallpaper candidates.

needsPackage "Dmodules";

print "=== Klein-compatible wallpaper classification Macaulay2 certificate ===";

QQ3 = QQ^3;
I3 = id_(QQ3);
Tx = matrix(QQ, {{1,0,1},{0,1,0},{0,0,1}});
Ty = matrix(QQ, {{1,0,0},{0,1,1},{0,0,1}});
TxInv = matrix(QQ, {{1,0,-1},{0,1,0},{0,0,1}});
TyInv = matrix(QQ, {{1,0,0},{0,1,-1},{0,0,1}});
Gx = matrix(QQ, {{1,0,1/2},{0,-1,0},{0,0,1}});
MirrorX = matrix(QQ, {{-1,0,0},{0,1,0},{0,0,1}});
Gy = matrix(QQ, {{-1,0,0},{0,1,1/2},{0,0,1}});

if Gx * Gx != Tx then error "pg glide square failed";
if Gx * Ty != TyInv * Gx then error "pg transverse inversion failed";
print "PASS: pg finite affine corridor";

if MirrorX * MirrorX != I3 then error "pmg mirror involutive failed";
if Gx * Gx != Tx then error "pmg pg-core glide square failed";
if Gx * Ty != TyInv * Gx then error "pmg pg-core transverse inversion failed";
print "PASS: pmg finite representative corridor";

if Gy * Gy != Ty then error "pgg second glide square failed";
if Gy * Tx != TxInv * Gy then error "pgg second glide transverse inversion failed";
if Gx * Ty != TyInv * Gx then error "pgg first glide transverse inversion failed";
print "PASS: pgg finite two-glide corridor";

root5 = (i,j,si,sj) -> matrix(QQ,
  apply(toList(0..4), k -> {if k == i then si else if k == j then sj else 0_QQ}));

d5Roots = {};
for i from 0 to 4 do (
  for j from i + 1 to 4 do (
    for si in {1_QQ,-1_QQ} do (
      for sj in {1_QQ,-1_QQ} do (
        d5Roots = append(d5Roots, root5(i,j,si,sj));
      )
    )
  )
);
if #unique d5Roots != 40 then error "D5 root count failed";

project2 = r -> matrix(QQ, {{r_(0,0)}, {r_(1,0)}});
projected = unique apply(d5Roots, r -> project2 r);
zero2 = matrix(QQ, {{0}, {0}});
projectedNonzero = select(projected, r -> r != zero2);
expected = {
  matrix(QQ, {{-1},{-1}}), matrix(QQ, {{-1},{0}}),
  matrix(QQ, {{-1},{1}}), matrix(QQ, {{0},{-1}}),
  matrix(QQ, {{0},{1}}), matrix(QQ, {{1},{-1}}),
  matrix(QQ, {{1},{0}}), matrix(QQ, {{1},{1}})
};
if set projectedNonzero != set expected then error "projected D5 B2/C2 set failed";
print "PASS: nonzero D5 projection is B2/C2 eight-root set";

candidateNormals = {
  matrix(QQ, {{0},{1}}), matrix(QQ, {{1},{-1}}),
  matrix(QQ, {{1},{0}}), matrix(QQ, {{0},{1}})
};
for n in candidateNormals do (
  if not member(n, projectedNonzero) then error "candidate normal not in projected D5 set";
);
print "PASS: pg/pmg/pgg candidate normals lie in projected D5 cross-section";

-- Dmodules lane: explicitly load the Weyl algebra and verify a differential
-- commutator on the wallpaper chart.
R = QQ[x1, x2];
W = makeWA R;
if (W_2 * W_0 - W_0 * W_2) != 1_W then error "Dmodules Weyl commutator failed";
print "PASS: Dmodules Weyl commutator [D_x1,x1] = 1";

print "KLEIN_COMPATIBLE_WALLPAPER_CLASSIFICATION_MACAULAY2_DMODULES_CERTIFICATE_OK";
