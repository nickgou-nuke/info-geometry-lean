# Machine-readable GAP export for the Sylow-2 PC carrier matrices.
Read("scripts/verify_carrier_u64_exact.g");
S := SylowSubgroup(G, 2);
psi := IsomorphismPcGroup(S);
P := Image(psi);
pcgs := Pcgs(P);
preimages := List(GeneratorsOfGroup(P), x -> PreImagesRepresentative(psi, x));
if Size(P) <> Product(RelativeOrders(pcgs)) then
  Error("GAP PC normal-form cardinality mismatch");
fi;
Print("PC_PRESENTATION_CARDINALITY_CHECK=true\n");
Print("PC_NORMAL_FORM_CARD=");
Print(Product(RelativeOrders(pcgs)));
Print("\n");
mat := fail;
support := fail;
Print("PC_RELATIVE_ORDERS=");
Print(RelativeOrders(pcgs));
Print("\n");
Print("PC_ACTUAL_ORDERS=");
Print(List(preimages, Order));
Print("\n");
for i in [1..Length(pcgs)] do
  relation := Image(psi, preimages[i]^RelativeOrders(pcgs)[i]);
  Print("PC_POWER_", i, "=");
  Print(ExponentsOfPcElement(pcgs, relation));
  Print("\n");
od;
for i in [2..Length(pcgs)] do
  for j in [1..i-1] do
    relation := Image(psi,
      preimages[i]^-1 * preimages[j] * preimages[i]);
    Print("PC_CONJ_", i, "_", j, "=");
    Print(ExponentsOfPcElement(pcgs, relation));
    Print("\n");
  od;
od;
for i in [1..Length(pcgs)] do
  relation := Image(psi, preimages[i]^RelativeOrders(pcgs)[i]);
  exponents := ExponentsOfPcElement(pcgs, relation);
  Print("PCPOWER ", i, " ", RelativeOrders(pcgs)[i], " ");
  for k in [1..Length(exponents)] do
    if k > 1 then Print(","); fi;
    Print(exponents[k]);
  od;
  Print("\n");
od;
for i in [2..Length(pcgs)] do
  for j in [1..i-1] do
    relation := Image(psi,
      preimages[i]^-1 * preimages[j] * preimages[i]);
    exponents := ExponentsOfPcElement(pcgs, relation);
    Print("PCCONJ ", i, " ", j, " ");
    for k in [1..Length(exponents)] do
      if k > 1 then Print(","); fi;
      Print(exponents[k]);
    od;
    Print("\n");
  od;
od;
for i in [1..Length(preimages)] do
  mat := preimages[i];
  rowSupports := [];
  for row in [1..8] do
    support := Filtered([1..8], col -> mat[row][col] <> Zero(GF(2)));
    Add(rowSupports, support);
    Print("PC_ROW_", i, "_", row, "=");
    Print(support);
    Print("\n");
  od;
  Print("PCROW ", i, " ");
  for row in [1..8] do
    if row > 1 then Print(";"); fi;
    for k in [1..Length(rowSupports[row])] do
      if k > 1 then Print(","); fi;
      Print(rowSupports[row][k]);
    od;
  od;
  Print("\n");
od;
QUIT;
