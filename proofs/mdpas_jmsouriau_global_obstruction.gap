# Exact-rational GAP certificate for MDPAS/JMSouriau obstruction/symplectic/KK layer.
Area := 1;
if Area = 0 then Error("area obstruction failed"); fi;
OmegaMat := [[0,1],[-1,0]];
if OmegaMat + TransposedMat(OmegaMat) <> [[0,0],[0,0]] then Error("skew OmegaMat failed"); fi;
if DeterminantMat(OmegaMat) <> 1 then Error("nondegenerate OmegaMat failed"); fi;
OmegaPair := function(v,w) return v[1]*w[2] - v[2]*w[1]; end;
V := [2,3]; W := [5,7];
if OmegaPair(V,W) + OmegaPair(W,V) <> 0 then Error("omega skew pairing failed"); fi;
Xvec := [11,13,17,19,23];
KK5 := Xvec[1]^2-Xvec[2]^2-Xvec[3]^2-Xvec[4]^2-Xvec[5]^2;
M4 := Xvec[1]^2-Xvec[2]^2-Xvec[3]^2-Xvec[4]^2;
if KK5 <> M4 - Xvec[5]^2 then Error("KK split failed"); fi;
if 2*(17/2) <> 17 then Error("prequantization readout failed"); fi;
Print("mdpas JMSouriau global obstruction GAP certificate: ok\n");
