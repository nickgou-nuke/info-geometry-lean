Print("PRIME_CUMULATIVE_CYCLOTOMIC_TOWER_GAP\n");
primes := [2,3,5,7,11,13];;
conductors := [];;
product := 1;;
for p in primes do product := product*p; Add(conductors,product); od;
for i in [1..Length(conductors)] do
  N := conductors[i];;
  if i > 1 and RemInt(N,conductors[i-1]) <> 0 then
    Error("conductor divisibility failure");
  fi;
  units := Filtered([1..N], a -> Gcd(a,N)=1);;
  Print("stage=",i-1," conductor=",N," degree=",Length(units),
    " unit_group_order=",Length(units),"\n");
od;
Print("STATUS=PASS\n");
