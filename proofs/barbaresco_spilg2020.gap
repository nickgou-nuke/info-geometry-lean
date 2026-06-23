# Exact-rational GAP certificate for Barbaresco SPIGL 2020 finite Souriau layer.
Brkt2 := function(A,B) return A*B - B*A; end;
Trace2 := function(A) return A[1][1] + A[2][2]; end;
KKS := function(MatF,A,B) return Trace2(MatF*Brkt2(A,B)); end;
MatX := [[1,2],[3,5]];
MatY := [[7,11],[13,17]];
MatZ := [[19,23],[29,31]];
MatF := [[37,41],[43,47]];
Z2 := [[0,0],[0,0]];
if Brkt2(MatX,MatX) <> Z2 then Error("self commutator failed"); fi;
if Brkt2(MatX,MatY) + Brkt2(MatY,MatX) <> Z2 then Error("skew commutator failed"); fi;
if Brkt2(MatX,Brkt2(MatY,MatZ)) + Brkt2(MatY,Brkt2(MatZ,MatX)) + Brkt2(MatZ,Brkt2(MatX,MatY)) <> Z2 then Error("Jacobi failed"); fi;
if KKS(MatF,MatX,MatX) <> 0 then Error("KKS alternating failed"); fi;
if KKS(MatF,MatX,MatY) + KKS(MatF,MatY,MatX) <> 0 then Error("KKS skew failed"); fi;
if KKS(MatF,MatX,Brkt2(MatY,MatZ)) + KKS(MatF,MatY,Brkt2(MatZ,MatX)) + KKS(MatF,MatZ,Brkt2(MatX,MatY)) <> 0 then Error("Souriau cocycle failed"); fi;
Massieu := function(t) return t^2/2; end;
if Massieu(6+1) - 2*Massieu(6) + Massieu(6-1) <> 1 then Error("Fisher difference failed"); fi;
Print("barbaresco SPIGL2020 GAP certificate: ok\n");
