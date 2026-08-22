F := GF(2);
s := PermutationMat((3,4)(6,7), 8, F);
c := PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F) *
     PermutationMat((3,4,5)(6,7,8), 8, F);
t := s * c;
for i in [1..8] do
  Print("TROW ", i, " ");
  for j in [1..8] do
    if t[i][j] <> Zero(F) then Print(j); fi;
    if j < 8 then Print(","); fi;
  od;
  Print("\n");
od;
QUIT;
