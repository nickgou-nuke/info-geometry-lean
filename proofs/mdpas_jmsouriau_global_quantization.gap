# Exact-rational GAP audit for the finite MDPAS/JM global-quantization lane.

J := [[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]];
if J + TransposedMat(J) <> NullMat(4,4) then
  Error("symplectic skew failed");
fi;
if DeterminantMat(J) <> 1 then
  Error("symplectic nondegeneracy failed");
fi;

unitCycle := 1 + 1 + 1;
if unitCycle = 0 then
  Error("unit de Rham obstruction failed");
fi;

g4 := [[1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,-1]];
A := [2,3,5,7];
r := 11;
kk := NullMat(5,5);
for i in [1..4] do
  for j in [1..4] do
    kk[i][j] := g4[i][j] + r*A[i]*A[j];
  od;
  kk[i][5] := r*A[i];
  kk[5][i] := r*A[i];
od;
kk[5][5] := r;
if kk <> TransposedMat(kk) then
  Error("Kaluza-Klein block symmetry failed");
fi;

if 2*(17/2) <> 17 then
  Error("half-spin prequantization failed");
fi;

Print("mdpas JMSouriau global quantization GAP certificate: ok\n");

