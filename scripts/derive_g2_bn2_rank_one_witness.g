# CAS derivation of an odd-coset rank-one witness for the fixed s-carrier.
F := GF(2);
entry := function(j, support)
  if j in support then return One(F); else return Zero(F); fi;
end;
rows := [
  [[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]],
  [[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]],
  [[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]],
  [[1],[2],[3],[4],[4,5],[6],[7,8],[8]],
  [[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]],
  [[1],[2],[3],[4],[3,5],[6,8],[7],[8]]
];
pcgens := List(rows, rs -> List([1..8], i -> List([1..8], j -> entry(j, rs[i]))));
B := Group(pcgens);
s := PermutationMat((3,4)(6,7), 8, F);
Hs := Group(pcgens{[1,3,4,5,6]});
odd := Filtered(Elements(B), r -> not r in Hs);
bs := Elements(B);
witness := First(odd, r -> ForAny(bs, b1 -> ForAny(bs, b2 ->
  s * r * s = b1 * s * b2)));
if witness = fail then Error("NO_RANK_ONE_WITNESS"); fi;
left := First(bs, b1 -> First(bs, b2 -> s * witness * s = b1 * s * b2) <> fail);
right := First(bs, b2 -> s * witness * s = left * s * b2);
Print("RANK_ONE_WITNESS=PASS\n");
Print("WITNESS_IN_B=", witness in B, "\n");
Print("WITNESS_IN_H=", witness in Hs, "\n");
Print("BIG_CELL_FACTORIZATION=", s * witness * s = left * s * right, "\n");

# Recover the two B-factors in the exact ordered Lean carrier basis.
bits := Tuples([0,1], 6);
pcword := function(v)
  local z, k;
  z := One(F)^0;
  for k in [1..6] do
    if v[k] = 1 then z := z * pcgens[k]; fi;
  od;
  return z;
end;
left_bits := First(bits, v -> pcword(v) = left);
right_bits := First(bits, v -> pcword(v) = right);
wit_bits := First(bits, v -> pcword(v) = witness);
if left_bits = fail or right_bits = fail or wit_bits = fail then
  Error("FIXED_LEAN_PC_RECOVERY_FAILED");
fi;
Print("FIXED_PC_RECOVERY=PASS\n");
Print("WITNESS_BITS=", wit_bits, "\n");
Print("LEFT_BITS=", left_bits, "\n");
Print("RIGHT_BITS=", right_bits, "\n");
QUIT;
