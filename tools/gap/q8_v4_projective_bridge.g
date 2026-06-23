# GAP exact finite certificate for the V4 / Q8 projective bridge.

RequireTrue := function(label, cond)
  if not cond then
    Error(Concatenation("FAILED: ", label));
  fi;
  Print("PASS: ", label, "\n");
end;

Print("=== V4 / Q8 GAP certificate ===\n");

Q := QuaternionGroup(8);
RequireTrue("Q8 order = 8", Size(Q) = 8);
RequireTrue("Q8 nonabelian", not IsAbelian(Q));
RequireTrue("Q8 center order = 2", Size(Centre(Q)) = 2);
RequireTrue("Q8 quotient order = 4", Size(FactorGroup(Q, Centre(Q))) = 4);
RequireTrue("Q8 quotient is V4", StructureDescription(FactorGroup(Q, Centre(Q))) = "C2 x C2");

gens := GeneratorsOfGroup(Q);
RequireTrue("Q8 has generators", Length(gens) >= 2);
RequireTrue("Q8 generator squares central",
  gens[1]^2 in Centre(Q) and gens[2]^2 in Centre(Q));
RequireTrue("Q8 commutator is central", Comm(gens[1], gens[2]) in Centre(Q));

Print("Q8_V4_PROJECTIVE_BRIDGE_GAP_CERTIFICATE_OK\n");
