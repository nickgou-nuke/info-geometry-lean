# Export the authoritative second simple Weyl representative.
# This is a matrix-orientation certificate only; it performs no carrier
# enumeration and does not construct double cosets.
F := GF(2);
S := PermutationMat((3,4)(6,7), 8, F);
H := PermutationMat((1,2)(3,6)(4,7)(5,8), 8, F);
W := H * S;
Print("WEYL9_MATRIX=");
for i in [1..8] do
  for j in [1..8] do
    if j > 1 then Print(","); fi;
    Print(Int(W[i][j]));
  od;
  if i < 8 then Print(";"); fi;
od;
Print("\nWEYL9_MATRIX_EXPORT=PASS\n");
QUIT;
