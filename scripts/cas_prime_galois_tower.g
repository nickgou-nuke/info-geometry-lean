# Exact finite arithmetic companion for the prime Galois tower.
Print("PRIME_GALOIS_TOWER_GAP\n");
primes := [2,3,5,7,11,13];;
for p in primes do
  units := Filtered([1..p-1], a -> Gcd(a,p)=1);;
  if Length(units) <> p-1 then Error("unit-group cardinality failure"); fi;
  # Multiplication modulo p is the explicit composition law for sigma_a.
  for a in units do for b in units do
    if not ((a*b) mod p) in units then Error("closure failure"); fi;
  od; od;
  Print("p=",p," degree=",p-1," galois_order=",Length(units),"\n");
od;
Print("STATUS=PASS\n");
