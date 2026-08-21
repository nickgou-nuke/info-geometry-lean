# Machine-readable GAP export for the Sylow-2 PC carrier matrices.
Read("scripts/verify_carrier_u64_exact.g");
S := SylowSubgroup(G, 2);
psi := IsomorphismPcGroup(S);
P := Image(psi);
pcgs := Pcgs(P);
preimages := List(GeneratorsOfGroup(P), x -> PreImagesRepresentative(psi, x));
mat := fail;
support := fail;
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
