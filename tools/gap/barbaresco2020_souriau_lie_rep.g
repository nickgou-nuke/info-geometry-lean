Print("=== GAP Barbaresco 2020 Souriau Lie representation certificate ===\n");

LieComm := function(A, B)
  return A * B - B * A;
end;

Zero2 := [[0, 0], [0, 0]];
Hmat := [[1, 0], [0, -1]];
Emat := [[0, 1], [0, 0]];
Fmat := [[0, 0], [1, 0]];

if LieComm(Hmat, Emat) <> 2 * Emat then
  Error("sl2 [H,E]=2E failed");
fi;
if LieComm(Hmat, Fmat) <> -2 * Fmat then
  Error("sl2 [H,F]=-2F failed");
fi;
if LieComm(Emat, Fmat) <> Hmat then
  Error("sl2 [E,F]=H failed");
fi;
Print("PASS: sl2 matrix brackets\n");

Zero3 := [[0, 0, 0], [0, 0, 0], [0, 0, 0]];
J := [[0, 0, 0], [0, 0, -1], [0, 1, 0]];
Kx := [[0, 1, 0], [1, 0, 0], [0, 0, 0]];
Ky := [[0, 0, 1], [0, 0, 0], [1, 0, 0]];

if LieComm(J, Kx) <> Ky then
  Error("so21 [J,Kx]=Ky failed");
fi;
if LieComm(J, Ky) <> -Kx then
  Error("so21 [J,Ky]=-Kx failed");
fi;
if LieComm(Kx, Ky) <> -J then
  Error("so21 [Kx,Ky]=-J failed");
fi;
Print("PASS: so(2,1) matrix brackets\n");

R := [[0, -1, 0], [1, 0, 0], [0, 0, 0]];
P1 := [[0, 0, 1], [0, 0, 0], [0, 0, 0]];
P2 := [[0, 0, 0], [0, 0, 1], [0, 0, 0]];

if LieComm(R, P1) <> P2 then
  Error("se2 [R,P1]=P2 failed");
fi;
if LieComm(R, P2) <> -P1 then
  Error("se2 [R,P2]=-P1 failed");
fi;
if LieComm(P1, P2) <> Zero3 then
  Error("se2 [P1,P2]=0 failed");
fi;
Print("PASS: se(2) matrix brackets\n");

if LieComm(R, LieComm(P1, P2)) + LieComm(P1, LieComm(P2, R)) + LieComm(P2, LieComm(R, P1)) <> Zero3 then
  Error("se2 Jacobi check failed");
fi;
if LieComm(J, LieComm(Kx, Ky)) + LieComm(Kx, LieComm(Ky, J)) + LieComm(Ky, LieComm(J, Kx)) <> Zero3 then
  Error("so21 Jacobi check failed");
fi;
Print("PASS: Jacobi checks for so(2,1) and se(2)\n");

Print("BARBARESCO2020_GAP_CERTIFICATE_OK\n");
