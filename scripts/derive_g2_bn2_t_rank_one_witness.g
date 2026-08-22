# CAS-only rank-one witness derivation for t on the fixed Lean carrier.
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
s := List([[1],[2],[4],[3],[5],[7],[6],[8]], r ->
     List([1..8], j -> entry(j, r)));
cycle := List([[1],[2],[4],[5],[3],[7],[8],[6]], r ->
     List([1..8], j -> entry(j, r)));
cartan := List([[2],[1],[6],[7],[8],[3],[4],[5]], r ->
     List([1..8], j -> entry(j, r)));
t := cartan * (s * cycle);
Ht := Group(pcgens{[2..6]});
if Size(B) <> 64 or Size(Ht) <> 32 or Index(B,Ht) <> 2 or
   Intersection(B,B^t) <> Ht then
  Error("T_RANK_ONE_LOCAL_GATE failed");
fi;
odd := Filtered(Elements(B), r -> not r in Ht);
bs := Elements(B);
witness := First(odd, r -> ForAny(bs, b1 -> ForAny(bs, b2 ->
  t * r * t = b1 * t * b2)));
if witness = fail then Error("NO_T_RANK_ONE_WITNESS"); fi;
left := First(bs, b1 -> First(bs, b2 ->
  t * witness * t = b1 * t * b2) <> fail);
right := First(bs, b2 -> t * witness * t = left * t * b2);
Print("T_RANK_ONE_WITNESS=PASS\n");
Print("T_WITNESS_IN_B=", witness in B, "\n");
Print("T_WITNESS_IN_H=", witness in Ht, "\n");
Print("T_BIG_CELL_FACTORIZATION=", t * witness * t = left * t * right, "\n");
Print("T_WITNESS_FACTORISATION="); Print(Factorization(B, witness)); Print("\n");
Print("T_LEFT_FACTORISATION="); Print(Factorization(B, left)); Print("\n");
Print("T_RIGHT_FACTORISATION="); Print(Factorization(B, right)); Print("\n");
pcword := function(v)
  local z, k;
  z := One(F)^0;
  for k in [6,5,4,3,2,1] do
    if v[k] = 1 then z := z * pcgens[k]; fi;
  od;
  return z;
end;
candidate := [1,0,0,1,0,0];
if pcword(candidate) <> witness then
  Error("T_WITNESS_ORDERED_PC_RECOVERY_FAILED");
fi;
Print("T_WITNESS_BITS=", candidate, "\n");
target := t * pcgens[2] * t;
if not target in B then Error("T_COMPLEMENT_CONJUGATE_NOT_IN_B"); fi;
Print("T_COMPLEMENT_P1_FACTORISATION="); Print(Factorization(B, target)); Print("\n");
candidate := [0,1,1,1,0,1];
if pcword(candidate) <> target then
  Error("T_COMPLEMENT_P1_ORDERED_PC_RECOVERY_FAILED");
fi;
Print("T_COMPLEMENT_P1_BITS=", candidate, "\n");
