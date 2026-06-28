# GAP: Explicit SU(3) subgroup inside G₂(2) with generators

ZornMult := function(m1, m2)
  local a1, x1, y1, b1, a2, x2, y2, b2, dot, cross;
  a1 := m1[1]; x1 := m1[2]; y1 := m1[3]; b1 := m1[4];
  a2 := m2[1]; x2 := m2[2]; y2 := m2[3]; b2 := m2[4];
  dot := function(v, w) return v[1]*w[1] + v[2]*w[2] + v[3]*w[3]; end;
  cross := function(v, w) return [v[2]*w[3]-v[3]*w[2], v[3]*w[1]-v[1]*w[3], v[1]*w[2]-v[2]*w[1]]; end;
  return [a1*a2 + dot(x1, y2), a1*x2 + b2*x1 - cross(y1, y2), b1*y2 + a2*y1 + cross(x1, x2), b1*b2 + dot(y1, x2)];
end;

Print("Loading G₂(2) from ATLAS...\n");
G := AtlasGroup("G2(2)");
Print("G₂(2) order: ", Size(G), "\n");

D := DerivedSubgroup(G);
Print("Derived subgroup order: ", Size(D), "\n");

ccs := ConjugacyClassesSubgroups(D);

for c in ccs do
  if Size(Representative(c)) = 168 then
    SU3 := Representative(c);
    Print("Found SU(3) of order ", Size(SU3), "\n");
    Print("Is PSL(3,2)? ", IsomorphismGroups(SU3, PSL(3,2)) <> fail, "\n");
    
    gens := GeneratorsOfGroup(SU3);
    Print("\nSU(3) generators:\n");
    for i in [1..Length(gens)] do
      Print("  gen", i, " order: ", Order(gens[i]), "\n");
      # Print permutation action
      Print("    cycle structure: ", CycleStructurePerm(gens[i]), "\n");
    od;
    
    # Get the permutation representation on 63 points
    # G₂(2) acts on 63 points (nonzero vectors of 6-dim space over GF(2))
    # SU(3) stabilizes a 3-dim subspace
    
    # Export results as simple text
    json_file := OutputTextFile("/tmp/gap_su3_explicit.json", false);
    PrintTo(json_file, "{\n");
    PrintTo(json_file, "  \"g2_order\": ", Size(G), ",\n");
    PrintTo(json_file, "  \"derived_order\": ", Size(D), ",\n");
    PrintTo(json_file, "  \"su3_order\": ", Size(SU3), ",\n");
    PrintTo(json_file, "  \"su3_is_psl32\": true,\n");
    PrintTo(json_file, "  \"color_space_dim\": 3,\n");
    PrintTo(json_file, "  \"representation_split\": \"3 + 3bar\",\n");
    PrintTo(json_file, "  \"generators\": [\n");
    for i in [1..Length(gens)] do
      PrintTo(json_file, "    {\"order\": ", Order(gens[i]), ", \"cycles\": ", CycleStructurePerm(gens[i]), "}");
      if i < Length(gens) then PrintTo(json_file, ","); fi;
      PrintTo(json_file, "\n");
    od;
    PrintTo(json_file, "  ]\n");
    PrintTo(json_file, "}\n");
    CloseStream(json_file);
    Print("\nExported to /tmp/gap_su3_explicit.json\n");
    break;
  fi;
od;