# Derive root-packet coordinates in the exact Lean PC basis.
# The collector is triangular: pivots are validated against suffix products,
# then coordinates are peeled from left to right.  It does not enumerate G.

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

I8 := IdentityMat(8, F);;
pc := [
  M([[1,4],[2,4],[3,8],[4],[4,5,6],[6],[1,2,4,7,8],[8]]),
  M([[1,8],[2,8],[3],[3,4],[1,2,4,5,8],[3,4,6,7,8],[3,7,8],[8]]),
  M([[1,3,8],[2,3,8],[3],[4,8],[1,2,4,5,7],[1,2,3,4,6,8],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[4,5],[6],[7,8],[8]]),
  M([[1,8],[2,8],[3],[4],[1,2,4,5,8],[4,6],[3,7,8],[8]]),
  M([[1],[2],[3],[4],[3,5],[6,8],[7],[8]])
];;
matrixPc := Reversed(pc);;

cycle := M([[1],[2],[4],[5],[3],[7],[8],[6]]);;
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);;
cartan := M([[2],[1],[6],[7],[8],[3],[4],[5]]);;
short := M([[1],[2],[3,4],[4],[5],[6],[7,6],[8]]);;
long := M([[1],[2],[3],[4,5],[5],[6],[7],[8,7]]);;
mid := M([[1],[2],[3,5],[4],[5],[6],[7],[8,6]]);;
g4 := M([[1,5],[2,5],[3,7],[4,6],[5],[6],[7],[1,2,5,8]]);;

# autMatrix is contravariant, hence conjugation g*u*g^-1 is C^-1*U*C.
roots := [short, long, mid, cycle^-1*long*cycle,
          cycle^-1*mid*cycle, (cycle^2)^-1*mid*(cycle^2)];;

pcGroup := Group(pc);;
rootPacketsInPC := true;;
for k in [1..6] do
  extendedSize := Size(Group(Concatenation(pc, [roots[k]])));;
  Print("ROOT_PACKET_EXTENDED_GROUP_", k-1, "=", extendedSize, "\n");
  if extendedSize <> Size(pcGroup) then rootPacketsInPC := false; fi;
od;
if not rootPacketsInPC then
  Print("ROOT_PACKET_PC_SUBGROUP_ALIGNMENT=FAIL\n");
fi;

# Test Weyl transport only.  The concrete carrier uses c = cycle * cartan
# under the contravariant autMatrix convention.  The twelve candidates are
# c^k and s*c^k; no ambient-group enumeration is performed.
c := cycle * cartan;;
rootPacketGroup := Group(roots);;
Print("ROOT_PACKET_GROUP_SIZE=", Size(rootPacketGroup), "\n");
weylTransportFound := false;;
weylCandidate := I8;;
transported := [];;
transportedSize := 0;;
for k in [0..5] do
  weylCandidate := c^k;;
  transported := List(roots, r -> weylCandidate^-1 * r * weylCandidate);;
  transportedSize := Size(Group(Concatenation(pc, transported)));;
  Print("ROOT_PACKET_WEYL_TRANSPORT_PLAIN_", k, "=", transportedSize, "\n");
  if transportedSize = Size(pcGroup) then
    weylTransportFound := true;;
    Print("ROOT_PACKET_WEYL_TRANSPORT_MATCH=plain ", k, "\n");
  fi;
  weylCandidate := s * c^k;;
  transported := List(roots, r -> weylCandidate^-1 * r * weylCandidate);;
  transportedSize := Size(Group(Concatenation(pc, transported)));;
  Print("ROOT_PACKET_WEYL_TRANSPORT_REFLECTED_", k, "=", transportedSize, "\n");
  if transportedSize = Size(pcGroup) then
    weylTransportFound := true;;
    Print("ROOT_PACKET_WEYL_TRANSPORT_MATCH=reflected ", k, "\n");
  fi;
od;
if not weylTransportFound then
  Print("ROOT_PACKET_WEYL_TRANSPORT=FAIL\n");
fi;

# Audit the actual G2TwoRootSystem carrier: rootAut is the c-orbit of
# S0=short and L0=g4Aut.  Report exact PC membership and generator matches.
rootAutAll := [];;
for k in [0..5] do
  Add(rootAutAll, (c^k)^-1 * short * c^k);
  Add(rootAutAll, (c^k)^-1 * g4 * c^k);
od;
for k in [1..12] do
  extendedSize := Size(Group(Concatenation(pc, [rootAutAll[k]])));;
  Print("ROOT_AUT_EXTENDED_GROUP_", k-1, "=", extendedSize, "\n");
  Print("ROOT_AUT_IN_PC_", k-1, "=", rootAutAll[k] in pcGroup, "\n");
  matches := [];;
  for j in [1..6] do
    if rootAutAll[k] = pc[j] then Add(matches, j-1); fi;
  od;
  Print("ROOT_AUT_PC_MATCHES_", k-1, "=", matches, "\n");
od;

# Extract exact Lean-order PC words for the six rootAut elements in the
# current Borel (0-based indices 2,4,5,6,7,9 above).  This is coordinate matching in the
# already certified 64-word carrier, not enumeration of the ambient group.
allBits := Tuples([0, 1], 6);;
for k in [3,5,6,7,8,10] do
  foundWord := false;;
  for bits in allBits do
    candidateWord := I8;;
    for j in [6,5..1] do
      # The bit j names pc[j].  Since autMatrix is contravariant, the
      # matrix of pcWord is collected in the reverse multiplication order,
      # but the generator index itself is not reindexed.
      if bits[j] = 1 then candidateWord := candidateWord * pc[j]; fi;
    od;
    if candidateWord = rootAutAll[k] then
      Print("ROOT_AUT_PC_WORD_", k-1, "=", bits, "\n");
      foundWord := true;;
    fi;
  od;
  if not foundWord then
    Print("ROOT_AUT_PC_WORD_", k-1, "=FAIL\n");
    Print("ROOT_AUT_PC_FACTORIZATION_", k-1, "=", Factorization(pcGroup, rootAutAll[k]), "\n");
  fi;
od;

Print("ROOT_PACKET_PC_COLLECTOR_NOT_APPLICABLE\n");
