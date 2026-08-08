Q := Rationals;;

A := 67;;
Z_As := 33;;
N_As := 34;;
Z_Se := 34;;
N_Se := 33;;
if Z_As <> N_Se then Error("Z_As <> N_Se"); fi;
if Z_Se <> N_As then Error("Z_Se <> N_As"); fi;

twoJi := 9;;
spinDen := twoJi + 1;;
MIV := 29 / 10000;;
MIS := 9 / 10000;;

BE1_As_725 := (MIV + MIS)^2 / spinDen;;
BE1_Se_717 := (MIV - MIS)^2 / spinDen;;
ratio := BE1_As_725 / BE1_Se_717;;
alpha := MIS / MIV;;

if BE1_As_725 <> 361 / 250000000 then Error("BE1_As_725"); fi;
if BE1_Se_717 <> 1 / 2500000 then Error("BE1_Se_717"); fi;
if ratio <> 361 / 100 then Error("ratio"); fi;
if alpha <> 9 / 29 then Error("alpha"); fi;

IVGMRKernel := function(A, e, R, DeltaE0, ri, rj)
  local C, oneBody, twoBody;
  C := ((A - 1) * e^2) / (4 * R * DeltaE0);
  oneBody := ri^3 / R^2;
  twoBody := ri * rj^2 / R^3;
  return C * (oneBody + twoBody);
end;;

unitKernel := IVGMRKernel(67, 1, 1, 20, 1, 1);;
if unitKernel <> 33 / 20 then Error("IVGMR unit kernel"); fi;

Print([BE1_As_725, BE1_Se_717, ratio, alpha, unitKernel], "\n");
