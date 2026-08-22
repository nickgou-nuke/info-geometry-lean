# Exact finite CAS audit for the concrete 8x8 F_2 carrier.
# This is an audit artifact only; it is not imported as a Lean axiom.
F := GF(2);
entry := function(j, support)
  if j in support then return One(F); else return Zero(F); fi;
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
B := Group(pcgens);
s := M([[1],[2],[4],[3],[5],[7],[6],[8]]);
cycle := M([[1],[2],[4],[5],[3],[7],[8],[6]]);
cartan := M([[2],[1],[6],[7],[8],[3],[4],[5]]);
w := [One(B), cycle, cycle^2, s, s*cycle, s*cycle^2,
      cartan, cartan*cycle, cartan*cycle^2, cartan*s,
      cartan*s*cycle, cartan*s*cycle^2];

G := Group(Concatenation(pcgens, [s, cycle, cartan]));
correctedT := cycle^2 * s * cartan;
leanC := cycle * cartan;
leanT := leanC * s;
apiGeneratedGroup := Group(Concatenation(pcgens, [s, leanT]));
leanW := [One(B), leanC, leanC^2, leanC^3, leanC^4, leanC^5,
  s, s*leanC, s*leanC^2, s*leanC^3, s*leanC^4, s*leanC^5];
leanCells := [];
for i in [1..12] do
  Add(leanCells, Set(Concatenation(List(Elements(B), b1 ->
    List(Elements(B), b2 -> b1*leanW[i]*b2)))));
od;
leanUnion := Set(Concatenation(leanCells));
leanDisjoint := true;
for i in [1..12] do
  for j in [i+1..12] do
    if Intersection(leanCells[i], leanCells[j]) <> [] then
      leanDisjoint := false;
    fi;
  od;
od;
correctedC := s * correctedT;
correctedW := [One(B), correctedC, correctedC^2, correctedC^3,
  correctedC^4, correctedC^5, s, s*correctedC, s*correctedC^2,
  s*correctedC^3, s*correctedC^4, s*correctedC^5];
correctedCells := [];
for i in [1..12] do
  Add(correctedCells, Set(Concatenation(List(Elements(B), b1 ->
    List(Elements(B), b2 -> b1*correctedW[i]*b2)))));
od;
correctedUnion := Set(Concatenation(correctedCells));
correctedDisjoint := true;
for i in [1..12] do
  for j in [i+1..12] do
    if Intersection(correctedCells[i], correctedCells[j]) <> [] then
      correctedDisjoint := false;
    fi;
  od;
od;
cells := [];
for i in [1..12] do
  Add(cells, Set(Concatenation(List(Elements(B), b1 ->
    List(Elements(B), b2 -> b1*w[i]*b2)))));
od;

union := Set(Concatenation(cells));
pairwise_disjoint := true;
for i in [1..12] do
  for j in [i+1..12] do
    if Intersection(cells[i], cells[j]) <> [] then
      pairwise_disjoint := false;
    fi;
  od;
od;

Print("TRUE_BRUHAT_GROUP_ORDER=", Size(G), "\n");
Print("LEAN_API_GENERATED_GROUP_ORDER=", Size(apiGeneratedGroup), "\n");
Print("TRUE_BRUHAT_SIMPLE_GENERATOR_ORDERS=", Order(s), ",", Order(cartan*(s*cycle)), ", product=", Order(s*(cartan*(s*cycle))), "\n");
Print("LEAN_CORRECTED_T_ORDERS=", Order(correctedT), ", product=", Order(s*correctedT), "\n");
Print("LEAN_API_T_ORDERS=", Order(leanT), ", product=", Order(s*leanT), "\n");
Print("LEAN_API_T_EQUALS_CORRECTED=", leanT = correctedT, "\n");
Print("LEAN_API_CELL_SIZES=", List(leanCells, Size), "\n");
Print("LEAN_API_UNION_SIZE=", Size(leanUnion), "\n");
if Size(leanUnion) = 12096 and leanDisjoint then
  Print("LEAN_API_BRUHAT_COVER=PASS\n");
else
  Print("LEAN_API_BRUHAT_COVER=FAIL\n");
fi;
Print("LEAN_CORRECTED_CELL_SIZES=", List(correctedCells, Size), "\n");
Print("LEAN_CORRECTED_UNION_SIZE=", Size(correctedUnion), "\n");
if Size(correctedUnion) = 12096 and correctedDisjoint then
  Print("LEAN_CORRECTED_BRUHAT_COVER=PASS\n");
else
  Print("LEAN_CORRECTED_BRUHAT_COVER=FAIL\n");
fi;
# Quotient-orbit readout on the exact carrier G/B, before the more expensive
# transition audit below.
# Lean's `QuotientGroup.mk` uses left cosets `gB` (relation
# `g⁻¹ * h ∈ B`) and left multiplication.  GAP's `RightCosets`/`OnRight`
# models the opposite orientation (`Bg`).  Use `LeftCosets`/`OnLeft` here so
# the exported orbit certificate has the same mathematical variance as Lean.
Q := LeftCosets(G, B);
# Explicit left translation on the left-coset carrier.  We do not use GAP's
# `OnRight`, whose variance is tied to `RightCosets`.
OnLeftCosets := function(q, g)
  local target, pos;
  target := Set(List(Elements(B), b -> (g * Representative(q)) * b));
  pos := Position(Q, target);
  if pos = fail then Error("left-coset action left the enumerated carrier"); fi;
  return Q[pos];
end;
flagAct := ActionHomomorphism(G, Q, OnLeftCosets);
BAct := Image(flagAct, B);
leanOrbits := [];
correctedOrbits := [];
for i in [1..12] do
  baseLean := PositionProperty(Q, q -> leanW[i] in q);
  baseCorrected := PositionProperty(Q, q -> correctedW[i] in q);
  Add(leanOrbits, Orbit(BAct, baseLean));
  Add(correctedOrbits, Orbit(BAct, baseCorrected));
od;
Print("LEAN_API_FLAG_ORBIT_SIZES=", List(leanOrbits, Length), "\n");
Print("LEAN_CORRECTED_FLAG_ORBIT_SIZES=", List(correctedOrbits, Length), "\n");
if Sum(List(leanOrbits, Length)) = 189 and
   Sum(List(correctedOrbits, Length)) = 189 then
  Print("EXACT_FLAG_ORBIT_PARTITIONS=PASS\n");
else
  Print("EXACT_FLAG_ORBIT_PARTITIONS=FAIL\n");
fi;
# Export the corrected orbit membership lists as a transport artifact.  The
# indices are GAP's 1-based coset enumeration; Lean import must subtract one
# and still prove the corresponding enumeration equivalence.
for i in [1..12] do
  Print("CORRECTED_FLAG_ORBIT_", i-1, "=", correctedOrbits[i], "\n");
od;
Print("TRUE_BRUHAT_CELL_SIZES=", List(cells, Size), "\n");
Print("TRUE_BRUHAT_UNION_SIZE=", Size(union), "\n");
if Size(G) = 12096 and Size(union) = 12096 and pairwise_disjoint then
Print("TRUE_BRUHAT_COVER=PASS\n");
else
  Print("TRUE_BRUHAT_COVER=FAIL\n");
fi;

# Probe exact word witnesses for the quotient representatives.  The generator
# list is fixed to the exact carrier order used above; these words are the
# round-trip data needed by a future Lean enum transport.
flagWordGens := Concatenation(pcgens, [s, correctedT]);
Gcorr := Group(flagWordGens);
for i in [1..Length(Q)] do
  fw := Factorization(Gcorr, Representative(Q[i]));
  Print("FLAG_REP_EXT_", i-1, "=", ExtRepOfObj(fw), "\n");
od;

QUIT;
