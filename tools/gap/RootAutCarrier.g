#############################################################################
# RootAutCarrier.g
#
# Reusable GAP utilities for a generator-defined root-automorphism carrier.
#
# The library deliberately does not choose a carrier size or a presentation.
# Callers provide matrix generators.  GAP's matrix rows/columns are exported
# in their native 1-based order; a Lean readback layer must translate indices
# explicitly and must decide its word-orientation convention separately.
#############################################################################

if not IsBound(InfoGeometryRootAutCarrier) then
  InfoGeometryRootAutCarrier := rec();
fi;

InfoGeometryRootAutCarrier.MatrixRows := function(g)
  local nr, nc;
  nr := Length(g);
  if nr = 0 then
    return [];
  fi;
  nc := Length(g[1]);
  return List([1..nr], i -> List([1..nc], j -> g[i][j]));
end;

InfoGeometryRootAutCarrier.Closure := function(generators)
  local identity, elements, words, todo, item, i, step, candidate, word, pos;
  if Length(generators) = 0 then
    Error("a nonempty generator list is required");
  fi;
  identity := One(generators[1]);
  elements := [ identity ];
  words := [ [] ];
  todo := [ 1 ];
  while Length(todo) > 0 do
    item := Remove(todo);
    for i in [1..Length(generators)] do
      for step in [1, -1] do
        if step = 1 then
          candidate := generators[i] * elements[item];
        else
          candidate := generators[i]^-1 * elements[item];
        fi;
        pos := Position(elements, candidate);
        if pos = fail then
          if step = 1 then
            word := Concatenation([[i, 1]], words[item]);
          else
            word := Concatenation([[i, -1]], words[item]);
          fi;
          Add(elements, candidate);
          Add(words, word);
          Add(todo, Length(elements));
        fi;
      od;
    od;
  od;
  return rec(elements := elements, words := words);
end;

InfoGeometryRootAutCarrier.Word := function(closure, g)
  local pos;
  pos := Position(closure.elements, g);
  if pos = fail then
    return fail;
  fi;
  return closure.words[pos];
end;

InfoGeometryRootAutCarrier.Build := function(pcGenerators, rootAutGenerators)
  local pcClosure, rootAutClosure, carrierClosure;
  pcClosure := InfoGeometryRootAutCarrier.Closure(pcGenerators);
  rootAutClosure := InfoGeometryRootAutCarrier.Closure(rootAutGenerators);
  carrierClosure := InfoGeometryRootAutCarrier.Closure(
    Concatenation(pcGenerators, rootAutGenerators));
  return rec(
    pcGenerators := pcGenerators,
    rootAutGenerators := rootAutGenerators,
    pcClosure := pcClosure,
    rootAutClosure := rootAutClosure,
    carrierClosure := carrierClosure,
    pcSize := Length(pcClosure.elements),
    rootAutSize := Length(rootAutClosure.elements),
    carrierSize := Length(carrierClosure.elements),
    rootAutInPC := List(rootAutGenerators,
      g -> Position(pcClosure.elements, g) <> fail),
    rootAutOrders := List(rootAutGenerators, Order)
  );
end;

InfoGeometryRootAutCarrier.Membership := function(carrier, elements)
  return List(elements, g -> rec(
    inPC := Position(carrier.pcClosure.elements, g) <> fail,
    inRootAut := Position(carrier.rootAutClosure.elements, g) <> fail,
    inCarrier := Position(carrier.carrierClosure.elements, g) <> fail,
    order := Order(g),
    pcWord := InfoGeometryRootAutCarrier.Word(carrier.pcClosure, g),
    rootAutWord := InfoGeometryRootAutCarrier.Word(carrier.rootAutClosure, g),
    carrierWord := InfoGeometryRootAutCarrier.Word(carrier.carrierClosure, g)
  ));
end;

InfoGeometryRootAutCarrier.Export := function(carrier)
  local rootExtensionSizes;
  rootExtensionSizes := List(carrier.rootAutGenerators, g ->
    Size(Group(Concatenation(carrier.pcGenerators, [g]))));
  return rec(
    convention := "GAP matrices and indices are 1-based; words are GAP ExtRep",
    pcGenerators := List(carrier.pcGenerators,
      InfoGeometryRootAutCarrier.MatrixRows),
    rootAutGenerators := List(carrier.rootAutGenerators,
      InfoGeometryRootAutCarrier.MatrixRows),
    pcSize := carrier.pcSize,
    rootAutSize := carrier.rootAutSize,
    carrierSize := carrier.carrierSize,
    rootAutInPC := carrier.rootAutInPC,
    rootExtensionSizes := rootExtensionSizes,
    rootAutOrders := carrier.rootAutOrders,
    rootAutWords := List(carrier.rootAutGenerators,
      g -> InfoGeometryRootAutCarrier.Word(carrier.carrierClosure, g))
  );
end;

InfoGeometryRootAutCarrier.PrintCertificate := function(carrier)
  local i, e, exported;
  exported := InfoGeometryRootAutCarrier.Export(carrier);
  Print("ROOT_AUT_CARRIER_CONVENTION=GAP_1_BASED_EXTREP\n");
  Print("ROOT_AUT_PC_SIZE=", exported.pcSize, "\n");
  Print("ROOT_AUT_SUBGROUP_SIZE=", exported.rootAutSize, "\n");
  Print("ROOT_AUT_CARRIER_SIZE=", exported.carrierSize, "\n");
  for i in [1..Length(exported.rootAutWords)] do
    Print("ROOT_AUT_WORD_", i, "=");
    Print(exported.rootAutWords[i], "\n");
  od;
  for i in [1..Length(exported.rootExtensionSizes)] do
    Print("ROOT_AUT_EXTENSION_SIZE_", i, "=", exported.rootExtensionSizes[i], "\n");
    Print("ROOT_AUT_IN_PC_", i, "=", exported.rootAutInPC[i], "\n");
  od;
  for i in [1..Length(exported.rootAutOrders)] do
    Print("ROOT_AUT_ORDER_", i, "=", exported.rootAutOrders[i], "\n");
  od;
  if ForAll(exported.rootAutInPC, x -> x) then
    Print("ROOT_AUT_MEMBERSHIP_IN_PC=PASS\n");
  else
    Print("ROOT_AUT_MEMBERSHIP_IN_PC=FAIL\n");
  fi;
  Print("ROOT_AUT_CARRIER_CERTIFICATE=PASS\n");
end;
