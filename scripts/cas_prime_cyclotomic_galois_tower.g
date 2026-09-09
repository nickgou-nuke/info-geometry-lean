#! /usr/bin/env gap
# Exact finite arithmetic certificate for the cumulative cyclotomic tower.

primes := [2,3,5,7,11,13];
moduli := [];
m := 1;
for p in primes do m := m*p; Add(moduli,m); od;

units := function(n)
  return Filtered([0..n-1], a -> Gcd(a,n) = 1);
end;

for n in moduli do
  U := units(n);
  if Length(U) <> Number(Filtered([1..n], k -> Gcd(k,n) = 1)) then
    Error("unit count failure");
  fi;
  for a in U do
    for b in U do
      if not ((a*b) mod n in U) then Error("unit closure failure"); fi;
    od;
  od;
od;

for i in [1..Length(moduli)-1] do
  low := moduli[i]; high := moduli[i+1];
  Ulow := units(low); Uhigh := units(high);
  image := Set(List(Uhigh, a -> a mod low));
  if image <> Set(Ulow) then Error("restriction is not surjective"); fi;
  kernel := Filtered(Uhigh, a -> a mod low = 1);
  if Length(kernel) * Length(Ulow) <> Length(Uhigh) then
    Error("kernel-image cardinality failure");
  fi;
od;

for i in [1..Length(moduli)-2] do
  a := moduli[i]; b := moduli[i+1]; c := moduli[i+2];
  for x in units(c) do
    if ((x mod b) mod a) <> (x mod a) then
      Error("restriction composition failure");
    fi;
  od;
od;

Print("PRIME_CYCLOTOMIC_GALOIS_TOWER\n");
Print("primes=",primes,"\n");
Print("moduli=",moduli,"\n");
Print("restriction_maps=surjective\n");
Print("restriction_composition=verified\n");
Print("STATUS=PASS\n");

