# Prime cyclotomic Galois tower finite-group certificate generator.
# External evidence only: Lean independently reproves the exported arithmetic facts.

primes := [2, 3, 5, 7, 11, 13];;
conductors := [];;
N := 1;;

Print("prime,conductor,phi\n");
for p in primes do
  N := N * p;
  Add(conductors, N);
  Print(p, ",", N, ",", Phi(N), "\n");
od;

Print("restriction_edges\n");
for i in [1..Length(conductors)-1] do
  Print(conductors[i], "->", conductors[i+1],
        ",quotient=", conductors[i+1]/conductors[i], "\n");
od;

# For squarefree N, Gal(Q(zeta_N)/Q) is represented arithmetically by
# (Z/NZ)^x.  GAP is used here only to expose the finite unit-group data.
for N in conductors do
  R := Integers mod N;
  U := Units(R);
  Print("units,", N, ",order,", Size(U),
        ",structure,", StructureDescription(U), "\n");
od;

QUIT;
