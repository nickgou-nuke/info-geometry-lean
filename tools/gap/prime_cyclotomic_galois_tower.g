# Six-prime cyclotomic Galois-tower evidence generator.
#
# This script is NOT trusted by Lean.  It emits explicit finite arithmetic
# data which is independently reproved by the Lean certificate owner.

primes := [2, 3, 5, 7, 11, 13];;
conductors := [];;
N := 1;;

for p in primes do
  if not IsPrimeInt(p) then
    Error("non-prime stage: ", p);
  fi;
  N := N * p;
  Add(conductors, N);
od;

EulerPhiByCount := function(n)
  return Length(Filtered([1..n], k -> GcdInt(k, n) = 1));
end;;

degrees := List(conductors, EulerPhiByCount);;

if conductors <> [2, 6, 30, 210, 2310, 30030] then
  Error("unexpected primorial conductor ledger");
fi;

if degrees <> [1, 2, 8, 48, 480, 5760] then
  Error("unexpected Euler-phi degree ledger");
fi;

for i in [1..Length(conductors)-1] do
  if conductors[i+1] mod conductors[i] <> 0 then
    Error("directed divisibility failure at stage ", i);
  fi;
od;

Print("primes      = ", primes, "\n");
Print("conductors  = ", conductors, "\n");
Print("phi/degrees = ", degrees, "\n");
Print("terminal    = ", conductors[Length(conductors)], "\n");

# Unit groups modulo N provide the standard arithmetic Galois model for
# cyclotomic extensions.  We only emit finite group orders/invariants here.
for N in conductors do
  G := Units(Integers mod N);
  Print("N = ", N,
        " | (Z/NZ)^x | = ", Size(G),
        " structure = ", StructureDescription(G), "\n");
od;
