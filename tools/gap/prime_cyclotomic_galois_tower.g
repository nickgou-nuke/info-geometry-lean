# GAP Cumulative Conductor Cyclotomic Galois Tower Certificate
# Primes: [2, 3, 5, 7, 11, 13]
# Conductors: [2, 6, 30, 210, 2310, 30030]

Print("======================================================================\n");
Print("GAP CAS: CUMULATIVE CYCLOTOMIC GALOIS TOWER\n");
Print("======================================================================\n");

primes := [2, 3, 5, 7, 11, 13];;
conductors := [2, 6, 30, 210, 2310, 30030];;
expected_totients := [1, 2, 8, 48, 480, 5760];;

for r in [1..Length(primes)] do
  p := primes[r];;
  N := conductors[r];;
  expected_phi := expected_totients[r];;

  if r > 1 then
    if N <> conductors[r-1] * p then
      Error("conductor recurrence mismatch");
    fi;
    if (N mod conductors[r-1]) <> 0 then
      Error("divisibility failure");
    fi;
  fi;

  # Unit group of Z/NZ
  units := Filtered([1..N-1], a -> Gcd(a, N) = 1);;
  if Length(units) <> expected_phi then
    Error("unit-group cardinality failure");
  fi;

  # Verify group closure under multiplication modulo N
  for a in units do
    for b in units do
      if not ((a * b) mod N) in units then
        Error("group closure failure");
      fi;
    od;
  od;

  Print("Stage ", r-1, ": p=", p, ", Conductor N=", N, ", Gal degree phi(N)=", Length(units), " [VERIFIED]\n");
od;

Print("\nAll 6 GAP Galois tower stages and unit groups: VERIFIED\n");
Print("======================================================================\n");
