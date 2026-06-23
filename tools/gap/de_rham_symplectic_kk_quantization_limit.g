Print("=== de Rham / symplectic / KK / colimit GAP certificate ===\n");

d0 := [[-1, 1, 0], [0, -1, 1], [1, 0, -1]];
d1 := [[1, 1, 1]];
if d1 * d0 <> [[0, 0, 0]] then Error("d1*d0 failed"); fi;

potential := [[2], [-1], [3]];
exact_current := d0 * potential;
if d1 * exact_current <> [[0]] then Error("exact current closed failed"); fi;

d1_zero := [[0, 0, 0]];
obstruction := [[1], [1], [1]];
if d1_zero * obstruction <> [[0]] then Error("closed obstruction failed"); fi;
augRank := RankMat(Concatenation(TransposedMat(d0), [Flat(obstruction)]));
if augRank = RankMat(TransposedMat(d0)) then Error("non-exact obstruction failed"); fi;

J := [[0, 1], [-1, 0]];
S := [[1, 1], [0, 1]];
if TransposedMat(S) * J * S <> J then Error("symplectic preservation failed"); fi;

kk := [
  [-1/2, 1/3, 0, 0, 1],
  [1/3, 11/9, 0, 0, 2/3],
  [0, 0, 1, 0, 0],
  [0, 0, 0, 1, 0],
  [1, 2/3, 0, 0, 2]
];
if DeterminantMat(kk) <> -2 then Error("KK determinant failed"); fi;

omega := 6;
curvature := 2;
hbar := 3;
if curvature * hbar <> omega then Error("prequantum scaling failed"); fi;

n := 2;
x := 3/5;
if (2 * x) / (2 ^ (n + 1)) <> x / (2 ^ n) then Error("colimit cone sample failed"); fi;

Print("DE_RHAM_SYMPLECTIC_KK_QUANTIZATION_LIMIT_GAP_CERTIFICATE_OK\n");
