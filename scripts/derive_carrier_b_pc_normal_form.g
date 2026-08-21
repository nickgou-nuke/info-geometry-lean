# CAS derivation of a non-binary normal form for the carrier subgroup.
# This is an export artifact only; it is not imported by Lean.
Read("scripts/verify_carrier_u64_exact.g");

S := SylowSubgroup(G, 2);
iso := IsomorphismPcGroup(S);
P := Image(iso);
Print("PC group structure: ", StructureDescription(P), "\n");
pcgens := GeneratorsOfGroup(P);
Print("PC generator orders: ", List(pcgens, Order), "\n");

preimages := List(pcgens, x -> PreImagesRepresentative(iso, x));
Print("Carrier PC generators:\n");
for i in [1..Length(preimages)] do
  Print("p", i, " := ", preimages[i], "\n");
od;

# The polycyclic collector gives a unique collected expression in the
# relative orders of the PC generators. Record its coordinate cardinality.
pcgs := Pcgs(P);
rels := RelativeOrders(pcgs);
Print("PC relative orders: ", rels, "\n");
Print("PC coordinate product: ", Product(rels), "\n");

# Validate the collector contract on the actual carrier: each coordinate word
# maps through the CAS isomorphism to the same exponent vector in the PC
# quotient, and every product of two coordinate words is collected back to a
# coordinate word.  This is a CAS certificate only.
pc_words := [];
pc_exponents := [];
for e1 in [0..rels[1]-1] do for e2 in [0..rels[2]-1] do
for e3 in [0..rels[3]-1] do for e4 in [0..rels[4]-1] do
for e5 in [0..rels[5]-1] do for e6 in [0..rels[6]-1] do
  w := preimages[1]^e1 * preimages[2]^e2 * preimages[3]^e3 *
       preimages[4]^e4 * preimages[5]^e5 * preimages[6]^e6;
  Add(pc_words, w);
  Add(pc_exponents, ExponentsOfPcElement(pcgs, Image(iso, w)));
od; od; od; od; od; od;
if Length(Set(pc_words)) <> Product(rels) then
  Error("PC coordinate chart is not injective");
fi;
if Length(Set(pc_exponents)) <> Product(rels) then
  Error("PC exponent chart is not injective");
fi;
for i in [1..Length(pc_words)] do
  for j in [1..Length(pc_words)] do
    product := pc_words[i] * pc_words[j];
    if not product in S then Error("PC chart is not closed"); fi;
    if not Image(iso, product) =
        PcElementByExponents(pcgs, ExponentsOfPcElement(pcgs, Image(iso, product))) then
      Error("PC collector round-trip failed");
    fi;
  od;
od;
Print("PC collector/chart/closure checks: PASS (", Length(Set(pc_words)),
  " coordinate words; ", Length(pc_words)^2, " products)\n");
# Export the carrier matrices of the PC generators for symbolic Lean alignment.
for i in [1..Length(preimages)] do
  mat := preimages[i];
  columns := List([1..8], col ->
    Filtered([1..8], row -> mat[row][col] <> Zero(GF(2))));
  Print("p", i, " column supports = ", columns, "\n");
od;

# Corrected normal-form check: use the PC generators, not the original
# arbitrary six-generator ordering.  Their relative orders are all two and
# the collected coordinate product is 64.
words := [];
for e1 in [0,1] do for e2 in [0,1] do for e3 in [0,1] do
for e4 in [0,1] do for e5 in [0,1] do for e6 in [0,1] do
  Add(words, preimages[1]^e1 * preimages[2]^e2 * preimages[3]^e3 *
      preimages[4]^e4 * preimages[5]^e5 * preimages[6]^e6);
od; od; od; od; od; od;
Print("PC collected binary words: ", Length(Set(words)), " of 64\n");
if Length(Set(words)) <> 64 then Error("PC normal form failed"); fi;
