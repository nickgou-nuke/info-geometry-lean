c := 5/4;;
s := 3/4;;
I2 := [[1,0],[0,1]];;
Z2 := [[0,0],[0,0]];;
Pp := [[1,0],[0,0]];;
Pm := [[0,0],[0,1]];;
eta := Pp - Pm;;
L := c*I2 - s*eta;;
R := c*I2 + s*eta;;
if Pp + Pm <> I2 then Error("partition failed"); fi;
if Pp*Pp <> Pp then Error("Pplus idempotent failed"); fi;
if Pm*Pm <> Pm then Error("Pminus idempotent failed"); fi;
if Pp*Pm <> Z2 then Error("orthogonality failed"); fi;
if Pm*Pp <> Z2 then Error("orthogonality failed"); fi;
if eta*eta <> I2 then Error("eta square failed"); fi;
if c*c - s*s <> 1 then Error("hyperbolic identity failed"); fi;
if L*R <> I2 then Error("left/right inverse failed"); fi;
if R*L <> I2 then Error("right/left inverse failed"); fi;
for i in [1..2] do
  for j in [1..2] do
    Obs := [[0,0],[0,0]];;
    Obs[i][j] := 1;;
    Dlt := L*Obs*R;;
    Tom := L*TransposedMat(Dlt)*R;;
    if Tom <> TransposedMat(Obs) then Error("Tomita cancellation failed"); fi;
  od;
od;
Print("cuntz Tomita-Takesaki GAP certificate: ok\n");
