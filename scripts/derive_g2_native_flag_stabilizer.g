# Structural CAS probe for the native point/line flag stabilizer.
# The group action is on the orbit of the native point; GAP computes a
# stabilizer generating set, rather than enumerating the 12096 group elements.
F := GF(2);
entry := function(j, r)
  if j in r then return One(F); else return Zero(F); fi;
end;
M := function(rows)
  return List(rows, r -> List([1..8], j -> entry(j, r)));
end;
pcgens := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);
c := M([[1],[2],[4],[5],[3],[7],[8],[6]]);
h := M([[2],[1],[6],[7],[8],[3],[4],[5]]);
G := Group(Concatenation(pcgens, [s, c^2*s*h]));
U := Group(pcgens);
leanPcMatrix := function(bits)
  local r, i;
  r := One(U);
  for i in [6,5,4,3,2,1] do
    if bits[i] = 1 then r := pcgens[i] * r; fi;
  od;
  return r;
end;
allBits := [];
for mask in [0..63] do
  Add(allBits, List([0..5], i -> (Int(mask / 2^i) mod 2)));
od;
OnLeft := function(v, g) return g^-1 * v; end;
p := [Zero(F), Zero(F), Zero(F), Zero(F), One(F), Zero(F), Zero(F), Zero(F)];
y := [Zero(F), Zero(F), Zero(F), Zero(F), Zero(F), One(F), Zero(F), Zero(F)];
points := Orbit(G, p, OnLeft);
if Length(points) <> 63 then Error("NATIVE_POINT_ORBIT failed"); fi;
line := Set([p, y, p + y]);
Print("PC_POINT_FIX=", ForAll(pcgens,
  function(g) return OnLeft(p, g) = p; end), "\n");
Print("PC_LINE_FIX=", ForAll(pcgens,
  function(g) return Set(List(AsSet(line), v -> OnLeft(v, g))) = line; end), "\n");
pointAction := ActionHomomorphism(G, points, OnLeft);
lineIndices := Set(List(line, v -> Position(points, v)));
Pact := Image(pointAction, Stabilizer(G, p, OnLeft));
Print("POINT_STAB_SIZE=", Size(Pact), " LINE_ORBIT_SIZE=",
  Length(Orbit(Pact, lineIndices, OnSets)), "\n");
stab := Stabilizer(Pact, lineIndices, OnSets);
Print("G_SIZE=", Size(G), " U_SIZE=", Size(U), " U_IN_STAB=",
  IsSubgroup(stab, Image(pointAction, U)), "\n");
Print("NATIVE_POINT_ORBIT_SIZE=", Length(points), "\n");
Print("NATIVE_FLAG_STABILIZER_SIZE=", Size(stab), "\n");
Print("NATIVE_FLAG_STABILIZER_GENERATORS=", Length(GeneratorsOfGroup(stab)), "\n");
emit := function(sg)
  local pre, bits;
  pre := PreImagesRepresentative(pointAction, sg);
  Print("NATIVE_FLAG_PC_WORD=", ExtRepOfObj(Factorization(U, pre)), "\n");
  bits := First(allBits, function(b) return leanPcMatrix(b) = pre; end);
  if bits = fail then Error("LEAN_PC_WORD_TRANSLATION failed"); fi;
  Print("NATIVE_FLAG_LEAN_BITS=", bits, "\n");
end;
for sg in GeneratorsOfGroup(stab) do emit(sg); od;
if Size(stab) = 64 then Print("NATIVE_FLAG_STABILIZER_CAS=PASS\n");
else Print("NATIVE_FLAG_STABILIZER_CAS=FAIL\n"); fi;
QUIT;
