# Machine-readable GAP export for the Sylow-2 PC carrier matrices.
Read("scripts/verify_carrier_u64_exact.g");
S := SylowSubgroup(G, 2);
psi := IsomorphismPcGroup(S);
P := Image(psi);
pcgs := Pcgs(P);
preimages := List(GeneratorsOfGroup(P), x -> PreImagesRepresentative(psi, x));
mat := fail;
support := fail;
Print("PC_RELORD=");
Print(RelativeOrders(pcgs));
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
for i in [1..Length(preimages)] do
  mat := preimages[i];
  for row in [1..8] do
    support := Filtered([1..8], col -> mat[row][col] <> Zero(GF(2)));
    Print("PC_ROW_", i, "_", row, "=");
    Print(support);
    Print("\n");
  od;
od;
QUIT;
