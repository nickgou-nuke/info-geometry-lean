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

# The projected action above loses the distinction between elements with the
# same point permutation.  Compute the stabilizer of the actual base flag in
# G instead: this is the carrier whose generators may be transported to Lean.
OnFlag := function(F, g)
  return [OnLeft(F[1], g),
    Set(List(AsSet(F[2]), v -> OnLeft(v, g)))];
end;
flagStabDirect := Stabilizer(G, [p, line], OnFlag);
Print("DIRECT_FLAG_STABILIZER_SIZE=", Size(flagStabDirect), "\n");
Print("DIRECT_FLAG_STABILIZER_GENERATORS=", Length(GeneratorsOfGroup(flagStabDirect)), "\n");
Print("DIRECT_FLAG_EQUALS_U=", flagStabDirect = U, "\n");
Print("DIRECT_FLAG_BASIS8_2_ORBIT=\n");
orbitBasis8Two := Orbit(flagStabDirect,
  [Zero(F),Zero(F),One(F),Zero(F),Zero(F),Zero(F),Zero(F),Zero(F)], OnLeft);
Print("DIRECT_FLAG_BASIS8_2_ORBIT_SIZE=", Length(orbitBasis8Two), "\n");
for v in orbitBasis8Two do
  Print(List(v, x -> Int(x)), "\n");
od;
Print("DIRECT_FLAG_BASIS8_7_ORBIT=\n");
orbitBasis8Seven := Orbit(flagStabDirect,
  [Zero(F),Zero(F),Zero(F),Zero(F),Zero(F),Zero(F),Zero(F),One(F)], OnLeft);
Print("DIRECT_FLAG_BASIS8_7_ORBIT_SIZE=", Length(orbitBasis8Seven), "\n");
for v in orbitBasis8Seven do
  Print(List(v, x -> Int(x)), "\n");
od;
Print("DIRECT_FLAG_PEEL2_CORRECTION_VECTOR_ORBIT=\n");
peel2CorrectionVector :=
  [One(F), One(F), Zero(F), One(F), Zero(F), Zero(F), One(F), One(F)];
orbitPeel2Correction := Orbit(flagStabDirect,
  peel2CorrectionVector, OnLeft);
Print("DIRECT_FLAG_PEEL2_CORRECTION_ORBIT_SIZE=",
  Length(orbitPeel2Correction), "\n");
for v in orbitPeel2Correction do
  Print(List(v, x -> Int(x)), "\n");
od;
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
  if pre = fail then
    Print("NATIVE_FLAG_PREIMAGE_FAIL\n");
    return;
  fi;
  if Factorization(U, pre) = fail then
    Print("NATIVE_FLAG_PREIMAGE_NOT_IN_U\n");
    return;
  fi;
  Print("NATIVE_FLAG_PC_WORD=", ExtRepOfObj(Factorization(U, pre)), "\n");
  bits := First(allBits, function(b) return leanPcMatrix(b) = pre; end);
  if bits = fail then Error("LEAN_PC_WORD_TRANSLATION failed"); fi;
  Print("NATIVE_FLAG_LEAN_BITS=", bits, "\n");
end;
emitDirect := function(pre)
  local bits;
  if Factorization(U, pre) = fail then
    Print("DIRECT_FLAG_GENERATOR_NOT_IN_U\n");
    return;
  fi;
  Print("DIRECT_FLAG_PC_WORD=", ExtRepOfObj(Factorization(U, pre)), "\n");
  bits := First(allBits, function(b) return leanPcMatrix(b) = pre; end);
  if bits = fail then Error("DIRECT_LEAN_PC_WORD_TRANSLATION failed"); fi;
  Print("DIRECT_FLAG_LEAN_BITS=", bits, "\n");
end;
Print("POINT_STABILIZER_GENERATORS=", Length(GeneratorsOfGroup(Pact)), "\n");
for sg in GeneratorsOfGroup(Pact) do emit(sg); od;
Print("DIRECT_FLAG_GENERATOR_READBACK=\n");
for sg in GeneratorsOfGroup(flagStabDirect) do emitDirect(sg); od;
for name in ["s", "c2sh"] do
  x := s;
  if name = "c2sh" then x := c^2*s*h; fi;
  Print("AMBIENT_", name, "_FIXES_POINT=", OnLeft(p, x) = p,
    "_LINE_IMAGE=", OnSets(lineIndices, Image(pointAction, x)), "\n");
od;
for i in [1..6] do
  for side in [1,2] do
    x := pcgens[i] * s;
    if side = 2 then x := s * pcgens[i]; fi;
    if OnLeft(p, x) = p then
      Print("PRODUCT_", i, "_", side, "_LINE_IMAGE=",
        OnSets(lineIndices, Image(pointAction, x)), "\n");
    fi;
  od;
od;
for sg in GeneratorsOfGroup(stab) do emit(sg); od;
if Size(stab) = 64 then Print("NATIVE_FLAG_STABILIZER_CAS=PASS\n");
else Print("NATIVE_FLAG_STABILIZER_CAS=FAIL\n"); fi;
QUIT;
