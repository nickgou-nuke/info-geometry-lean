PairCount := function(n)
  return n * (n - 1) / 2;
end;

FourBodyCount := function(N)
  return N * (N - 1) * (N - 2) * (N - 3) / 24;
end;

SKPoolSize := function(L)
  return 2 * PairCount(L);
end;

SYKPoolSize := function(n)
  return n + 3 * PairCount(n);
end;

DenseSYKDLA := function(n)
  return 2^(2*n - 1) - 2;
end;

SKDLA := function(L)
  return 2 * (4^(L - 1) - 1);
end;

if FourBodyCount(20) <> 4845 then Error("dense terms"); fi;
if 20 / 2 <> 10 then Error("majorana qubits"); fi;
if 9 * 20 <> 180 then Error("sparse terms"); fi;
if (4845 - 180) / 4845 <> 311 / 323 then Error("removal ratio"); fi;
if SKPoolSize(18) <> 306 then Error("SK pool"); fi;
if SYKPoolSize(10) <> 145 then Error("SYK pool"); fi;
if PairCount(18) + 18 <> 171 then Error("SK terms"); fi;
if 2^10 <> 1024 then Error("Hilbert dim"); fi;
if AbsInt(NumeratorRat(275/100 - 278/100)) / DenominatorRat(275/100 - 278/100) <> 3/100 then Error("entropy"); fi;
if not (9936/10000 >= 993/1000) then Error("dense fidelity"); fi;
if not (9966/10000 >= 993/1000) then Error("sparse fidelity"); fi;
if DenseSYKDLA(10) <> 524286 then Error("DLA"); fi;
if SKDLA(4) <> 126 then Error("SK DLA"); fi;

Print(rec(
  denseSYKTermsN20 := FourBodyCount(20),
  sparseSYKTermsN20 := 9 * 20,
  SKPoolL18 := SKPoolSize(18),
  SYKPoolN10 := SYKPoolSize(10),
  hilbertDimN20 := 2^10
), "\n");

QUIT;
