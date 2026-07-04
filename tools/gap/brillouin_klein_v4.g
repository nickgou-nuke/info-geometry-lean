Q := NullMat(10, 10);
for i in [1..5] do
    Q[i][i+5] := 1;
    Q[i+5][i] := 1;
od;

reflPair0 := IdentityMat(10);
reflPair0[1][1] := -1;
reflPair0[6][6] := -1;

reflPair1 := IdentityMat(10);
reflPair1[2][2] := -1;
reflPair1[7][7] := -1;

Print("Testing reflPair0^2 = I: ", reflPair0^2 = IdentityMat(10), "\n");
Print("Testing reflPair1^2 = I: ", reflPair1^2 = IdentityMat(10), "\n");
Print("Testing commute: ", reflPair0 * reflPair1 = reflPair1 * reflPair0, "\n");
Print("Testing reflPair0 preserves Q: ", TransposedMat(reflPair0) * Q * reflPair0 = Q, "\n");
Print("Testing reflPair1 preserves Q: ", TransposedMat(reflPair1) * Q * reflPair1 = Q, "\n");

QUIT;
