# Fixed-basis CAS certificate for the explicit Lean PC carrier.
#
# This owner intentionally does not call SylowSubgroup, Pcgs, or any other
# arbitrary GAP coordinate system.  The ordered matrices below are copied
# from G2LeanCarrierMatrixAlignment.lean and all products are computed in that
# exact Lean basis.
F := GF(2);;
M := function(rows)
  local m, i, j;
  m := [];
  for i in [1..8] do
    Add(m, []);
    for j in [1..8] do
      if j in rows[i] then Add(m[i], One(F));
      else Add(m[i], Zero(F)); fi;
    od;
  od;
  return m;
end;;

leanGens := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];;

s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);;
B := Group(leanGens);;
if Size(B) <> 64 then Error("LEAN_FIXED_CARRIER_SIZE_FAIL"); fi;;
Print("LEAN_FIXED_CARRIER_SIZE=PASS\n");

# Lean automorphism composition is represented contravariantly by autMatrix.
# These are the five complement conjugations proved in the Lean owner.
targets := [
  s^-1 * leanGens[1] * s,
  s^-1 * leanGens[3] * s,
  s^-1 * leanGens[4] * s,
  s^-1 * leanGens[5] * s,
  s^-1 * leanGens[6] * s
];;
expected := [
  leanGens[6] * leanGens[5] * leanGens[3],
  leanGens[6] * leanGens[5] * leanGens[1],
  leanGens[6],
  leanGens[6] * leanGens[5] * leanGens[4],
  leanGens[4]
];;
for k in [1..5] do
  if targets[k] <> expected[k] then
    Error("LEAN_FIXED_COMPLEMENT_CONJUGATION_FAIL_", k);
  fi;
od;
Print("LEAN_FIXED_COMPLEMENT_CONJUGATIONS=PASS\n");
Print("LEAN_FIXED_CARRIER_ALIGNMENT=PASS\n");
QUIT;
